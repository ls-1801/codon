// Copyright (C) 2022-2026 Exaloop Inc. <https://exaloop.io>

#include "codon/parser/ast.h"
#include "codon/parser/common.h"
#include "codon/parser/match.h"
#include "codon/parser/visitors/format/format.h"
#include "codon/parser/visitors/typecheck/typecheck.h"

namespace codon::ast {

using namespace types;
using namespace matcher;
using namespace error;

/// Transform asserts.
/// @example
///   `assert foo()` ->
///   `if not foo(): raise __internal__.seq_assert([file], [line], "")`
///   `assert foo(), msg` ->
///   `if not foo(): raise __internal__.seq_assert([file], [line], str(msg))`
/// Use `seq_assert_test` instead of `seq_assert` and do not raise anything during unit
/// testing (i.e., when the enclosing function is marked with `@test`).
void TypecheckVisitor::visit(AssertStmt *stmt) {
  Expr *msg = N<StringExpr>("");
  if (stmt->getMessage())
    msg = N<CallExpr>(N<IdExpr>("str"), stmt->getMessage());
  auto test = ctx->inFunction() && ctx->getBase()->func->hasAttribute(Attr::Test);
  auto ex = N<CallExpr>(
      N<DotExpr>(N<IdExpr>("__internal__"), test ? "seq_assert_test" : "seq_assert"),
      N<StringExpr>(stmt->getSrcInfo().file), N<IntExpr>(stmt->getSrcInfo().line), msg);
  auto cond = N<UnaryExpr>("!", stmt->getExpr());
  if (test) {
    resultStmt = transform(N<IfStmt>(cond, N<ExprStmt>(ex)));
  } else {
    resultStmt = transform(N<IfStmt>(cond, N<ThrowStmt>(ex)));
  }
}

/// Typecheck try-except statements. Handle Python exceptions separately.
/// @example
///   ```try: ...
///      except python.Error as e: ...
///      except PyExc as f: ...
///      except ValueError as g: ...
///   ``` -> ```
///      try: ...
///      except ValueError as g: ...                   # ValueError
///      except PyExc as exc:
///        while True:
///          if isinstance(exc.pytype, python.Error):  # python.Error
///            e = exc.pytype; ...; break
///          f = exc; ...; break                       # PyExc
///          raise```
/// NES: Python code imports an optional module in a `try` and falls back in the handler:
///   try:
///       from _speedups import f
///   except ImportError:
///       def f(x): ...
/// If such an import names a module that Codon does not find, and a handler of the `try` catches ImportError (as
/// ImportError, ModuleNotFoundError, Exception, BaseException, in a tuple, or bare), the `try` statement becomes the
/// statements before the import, the first such handler, and the `finally` suite: what Python runs. Codon would
/// otherwise reject the whole module at compile time. If every import is found, the `try` statement becomes its body,
/// `else` and `finally` suites.
Stmt *TypecheckVisitor::transformImportFallback(TryStmt *stmt) {
  if (ctx->autoPython)
    return nullptr;
  auto catchesImportError = [](Expr *e) {
    if (!e)
      return true;
    auto ok = [](Expr *x) {
      for (auto n : {"ImportError", "ModuleNotFoundError", "Exception", "BaseException"})
        if (isId(x, n))
          return true;
      return false;
    };
    if (ok(e))
      return true;
    if (auto t = cast<TupleExpr>(e))
      for (auto *x : *t)
        if (ok(x))
          return true;
    return false;
  };
  ExceptStmt *handler = nullptr;
  for (auto &c : *stmt)
    if (catchesImportError(c->getException())) {
      handler = c;
      break;
    }
  if (!handler)
    return nullptr;
  std::vector<Stmt *> before;
  for (auto *s : *stmt->getSuite()) {
    auto imp = cast<ImportStmt>(s);
    if (!imp)
      return nullptr; // only a leading run of imports (and nothing that could raise first)
    if (match(imp->getFrom(), M<IdExpr>(MOr("C", "python"))))
      return nullptr;
    auto components = getImportPath(imp->getFrom(), imp->getDots());
    auto file = getImportFile(ctx->cache, combine2(components, "/"), ctx->getFilename(), false,
                              imp->getDots() > 0);
    if (!file) {
      auto suite = N<SuiteStmt>(before);
      auto module = FormatVisitor::apply(imp->getFrom());
      if (!handler->getVar().empty())
        suite->addStmt(N<AssignStmt>(
            N<IdExpr>(handler->getVar()),
            N<CallExpr>(N<IdExpr>("ModuleNotFoundError"),
                        N<StringExpr>(fmt::format("No module named '{}'", module)))));
      suite->addStmt(clean_clone(handler->getSuite()));
      if (stmt->getFinally())
        suite->addStmt(clean_clone(stmt->getFinally()));
      return suite;
    }
    before.push_back(clean_clone(s));
  }
  // Every import is found: the handlers cannot run (an import of a missing name is a compile-time error), and their
  // code may not type-check (`except ImportError: cache = None` after `from functools import cache`). The `try`
  // statement becomes its body, its `else` suite and its `finally` suite.
  auto suite = N<SuiteStmt>(before);
  if (stmt->getElse())
    suite->addStmt(clean_clone(stmt->getElse()));
  if (stmt->getFinally())
    suite->addStmt(clean_clone(stmt->getFinally()));
  return suite;
}

void TypecheckVisitor::visit(TryStmt *stmt) {
  if (auto fallback = transformImportFallback(stmt)) {
    resultStmt = transform(fallback);
    return;
  }
  ctx->blockLevel++;
  stmt->suite = SuiteStmt::wrap(transform(stmt->getSuite()));
  ctx->blockLevel--;

  std::vector<ExceptStmt *> catches;
  auto pyCatchStmt = N<WhileStmt>(N<BoolExpr>(true), N<SuiteStmt>());

  auto done = stmt->getSuite()->isDone();
  for (auto &c : *stmt) {
    TypeContext::Item val = nullptr;
    if (!c->getVar().empty()) {
      if (!c->hasAttribute(Attr::ExprDominated) &&
          !c->hasAttribute(Attr::ExprDominatedUsed)) {
        val = ctx->addVar(getUnmangledName(c->getVar()),
                          ctx->generateCanonicalName(c->getVar()), instantiateUnbound(),
                          getTime());
      } else if (c->hasAttribute(Attr::ExprDominatedUsed)) {
        val = ctx->forceFind(c->getVar());
        c->eraseAttribute(Attr::ExprDominatedUsed);
        c->setAttribute(Attr::ExprDominated);
        c->suite = N<SuiteStmt>(
            N<AssignStmt>(N<IdExpr>(fmt::format("{}{}", getUnmangledName(c->getVar()),
                                                VAR_USED_SUFFIX)),
                          N<BoolExpr>(true), nullptr, AssignStmt::UpdateMode::Update),
            c->getSuite());
      } else {
        val = ctx->forceFind(c->getVar());
      }
      c->var = val->canonicalName;
    }
    c->exc = transform(c->getException());
    if (c->getException() && extractClassType(c->getException())->is("pyobj")) {
      // Transform python.Error exceptions

      if (!stmt->hasAttribute(Attr::TryPyVar))
        stmt->setAttribute(Attr::TryPyVar, getTemporaryVar("pyexc"));
      auto pyVar = stmt->getAttribute<ir::StringValueAttribute>(Attr::TryPyVar)->value;

      if (!c->var.empty()) {
        c->suite = N<SuiteStmt>(
            N<AssignStmt>(N<IdExpr>(c->var), N<DotExpr>(N<IdExpr>(pyVar), "pytype")),
            c->getSuite());
      }
      c->suite = SuiteStmt::wrap(N<IfStmt>(
          N<CallExpr>(N<IdExpr>("isinstance"), N<DotExpr>(N<IdExpr>(pyVar), "pytype"),
                      c->getException()),
          N<SuiteStmt>(c->getSuite(), N<BreakStmt>()), nullptr));
      cast<SuiteStmt>(pyCatchStmt->getSuite())->addStmt(c->getSuite());
    } else if (c->getException() &&
               extractClassType(c->getException())
                   ->is(getMangledClass("std.internal.python", "PyError"))) {
      // Transform PyExc exceptions
      if (!stmt->hasAttribute(Attr::TryPyVar))
        stmt->setAttribute(Attr::TryPyVar, getTemporaryVar("pyexc"));
      auto pyVar = stmt->getAttribute<ir::StringValueAttribute>(Attr::TryPyVar)->value;

      if (!c->var.empty()) {
        c->suite = N<SuiteStmt>(N<AssignStmt>(N<IdExpr>(c->var), N<IdExpr>(pyVar)),
                                c->getSuite());
      }
      c->suite = N<SuiteStmt>(c->getSuite(), N<BreakStmt>());
      cast<SuiteStmt>(pyCatchStmt->getSuite())->addStmt(c->getSuite());
    } else {
      // Handle all other exceptions
      c->exc = transformType(c->getException());

      if (c->getException()) {
        auto t = extractClassType(c->getException());
        bool exceptionOK = false;
        for (auto &p : getRTTISuperTypes(t))
          if (p->is(getMangledClass("std.internal.types.error", "BaseException"))) {
            exceptionOK = true;
            break;
          }
        if (!exceptionOK)
          E(Error::CATCH_EXCEPTION_TYPE, c->getException(), t->prettyString());
        if (val)
          unify(val->getType(), extractType(c->getException()));
      }
      ctx->blockLevel++;
      c->suite = SuiteStmt::wrap(transform(c->getSuite()));
      ctx->blockLevel--;
      done &= (!c->getException() || c->getException()->isDone()) &&
              c->getSuite()->isDone();
      catches.push_back(c);
    }
  }
  if (!cast<SuiteStmt>(pyCatchStmt->getSuite())->empty()) {
    // Process PyError catches
    auto pyVar = stmt->getAttribute<ir::StringValueAttribute>(Attr::TryPyVar)->value;
    auto exc = N<IdExpr>(getMangledClass("std.internal.python", "PyError"));
    cast<SuiteStmt>(pyCatchStmt->getSuite())->addStmt(N<ThrowStmt>(nullptr));
    auto c = N<ExceptStmt>(pyVar, transformType(exc), pyCatchStmt);

    auto val = ctx->addVar(
        pyVar, pyVar, extractType(c->getException())->shared_from_this(), getTime());
    ctx->blockLevel++;
    c->suite = SuiteStmt::wrap(transform(c->getSuite()));
    ctx->blockLevel--;
    done &= (!c->exc || c->exc->isDone()) && c->getSuite()->isDone();
    catches.push_back(c);
  }
  stmt->items = catches;

  if (stmt->getElse()) {
    ctx->blockLevel++;
    stmt->elseSuite = SuiteStmt::wrap(transform(stmt->getElse()));
    ctx->blockLevel--;
    done &= stmt->getElse()->isDone();
  }

  if (stmt->getFinally()) {
    ctx->blockLevel++;
    stmt->finally = SuiteStmt::wrap(transform(stmt->getFinally()));
    ctx->blockLevel--;
    done &= stmt->getFinally()->isDone();
  }

  if (done)
    stmt->setDone();
}

/// Transform `raise` statements.
/// @example
///   `raise exc` -> ```raise BaseException.set_header(exc, "fn", "file", line, col)```
void TypecheckVisitor::visit(ThrowStmt *stmt) {
  if (!stmt->expr) {
    stmt->setDone();
    return;
  }

  stmt->expr = transform(stmt->getExpr());
  // NES: wrap only once. After the first type-check round the callee of the wrapping call has its realized name, so the
  // match below failed, and every further round (while the exception's type is still open) wrapped the expression again:
  // the expression doubled per round, and compiling such a module did not end.
  if (!stmt->transformed &&
      !match(stmt->getExpr(),
             M<CallExpr>(M<IdExpr>(getMangledMethod("std.internal.types.error",
                                                    "BaseException", "_set_header")),
                         M_))) {
    stmt->transformed = true;
    stmt->expr = transform(N<CallExpr>(
        N<IdExpr>(getMangledMethod("std.internal.types.error", "BaseException",
                                   "_set_header")),
        stmt->getExpr(), N<StringExpr>(ctx->getBase()->name),
        N<StringExpr>(stmt->getSrcInfo().file), N<IntExpr>(stmt->getSrcInfo().line),
        N<IntExpr>(stmt->getSrcInfo().col),
        stmt->getFrom()
            ? N<CallExpr>(N<DotExpr>(N<IdExpr>("Super"), "_super"), stmt->getFrom(),
                          N<IdExpr>(getMangledClass("std.internal.types.error",
                                                    "BaseException")))
            : N<CallExpr>(N<IdExpr>("NoneType"))));
  }
  if (stmt->getExpr()->isDone())
    stmt->setDone();
}

/// Transform with statements.
/// @example
///   `with foo(), bar() as a: ...` ->
///   ```tmp = foo()
///      tmp.__enter__()
///      try:
///        a = bar()
///        a.__enter__()
///        try:
///          ...
///        finally:
///          a.__exit__()
///      finally:
///        tmp.__exit__()```
void TypecheckVisitor::visit(WithStmt *stmt) {
  seqassert(!stmt->empty(), "stmt->items is empty");

  bool isAsync = stmt->isAsync();

  std::vector<Stmt *> content;
  for (auto i = stmt->items.size(); i-- > 0;) {
    std::string var = stmt->vars[i].empty() ? getTemporaryVar("with") : stmt->vars[i];
    auto as = N<AssignStmt>(N<IdExpr>(var), (*stmt)[i], nullptr,
                            (*stmt)[i]->hasAttribute(Attr::ExprDominated)
                                ? AssignStmt::UpdateMode::Update
                                : AssignStmt::UpdateMode::Assign);

    Expr *enter =
        N<CallExpr>(N<DotExpr>(N<IdExpr>(var), isAsync ? "__aenter__" : "__enter__"));
    Expr *exit =
        N<CallExpr>(N<DotExpr>(N<IdExpr>(var), isAsync ? "__aexit__" : "__exit__"));
    if (isAsync) {
      enter = N<AwaitExpr>(enter);
      exit = N<AwaitExpr>(exit);
    }
    content = std::vector<Stmt *>{
        as, N<ExprStmt>(enter),
        N<TryStmt>(!content.empty() ? N<SuiteStmt>(content) : clone(stmt->getSuite()),
                   std::vector<ExceptStmt *>{}, nullptr,
                   N<SuiteStmt>(N<ExprStmt>(exit)))};
  }
  resultStmt = transform(N<SuiteStmt>(content));
}

} // namespace codon::ast
