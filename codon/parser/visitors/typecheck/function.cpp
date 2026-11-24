// Copyright (C) 2022-2026 Exaloop Inc. <https://exaloop.io>

#include <algorithm>
#include <string>
#include <tuple>

#include "codon/cir/attribute.h"
#include "codon/parser/ast.h"
#include "codon/parser/common.h"
#include "codon/parser/match.h"
#include "codon/parser/peg/peg.h"
#include "codon/parser/visitors/scoping/scoping.h"
#include "codon/parser/visitors/typecheck/typecheck.h"

using namespace codon::error;

namespace codon::ast {

using namespace types;
using namespace matcher;

/// Unify the function return type with `Generator[?]`.
/// The unbound type will be deduced from return/yield statements.
void TypecheckVisitor::visit(LambdaExpr *expr) {
  std::vector<Param> params;
  std::string name = getTemporaryVar("lambda");
  params.reserve(expr->size());
  for (auto &s : *expr)
    params.emplace_back(s);
  Stmt *f = N<FunctionStmt>(name, nullptr, params,
                            N<SuiteStmt>(N<ReturnStmt>(expr->getExpr())));

  /// TODO: just copy BindingsAttribute from expr instead?
  if (auto err = ScopingVisitor::apply(ctx->cache, N<SuiteStmt>(f)))
    throw exc::ParserException(std::move(err));
  f->setAttribute(Attr::ExprTime, getTime()); // to handle captures properly
  f = transform(f);
  if (auto a = expr->getAttribute(Attr::Bindings))
    f->setAttribute(Attr::Bindings, a->clone());
  prependStmts->push_back(f);
  resultExpr = transform(N<IdExpr>(name));
}

/// Unify the function return type with `Generator[?]`.
/// The unbound type will be deduced from return/yield statements.
void TypecheckVisitor::visit(YieldExpr *expr) {
  if (!ctx->inFunction())
    E(Error::FN_OUTSIDE_ERROR, expr, "yield");

  unify(ctx->getBase()->returnType.get(),
        instantiateType(getStdLibType("Generator"), {expr->getType()}));
  if (realize(expr->getType()))
    expr->setDone();
}

/// Typecheck await statements.
void TypecheckVisitor::visit(AwaitExpr *expr) {
  if (!ctx->inFunction())
    E(Error::FN_OUTSIDE_ERROR, expr, "await");
  auto isAsync = ctx->getBase()->func->isAsync();
  if (!isAsync)
    E(Error::FN_OUTSIDE_ERROR, expr, "await");

  expr->expr = transform(expr->getExpr());
  if (!expr->transformed) {
    if (auto c = expr->getExpr()->getType()->getClass()) {
      bool isCoroutine = c->is(getMangledClass("std.internal.core", "Coroutine")) ||
                         c->is(getMangledClass("std.asyncio", "Future")) ||
                         c->is(getMangledClass("std.asyncio", "Task"));
      if (!isCoroutine) {
        if (!findMethod(c, "__await__").empty()) {
          auto e = transform(N<CallExpr>(N<DotExpr>(expr->getExpr(), "__await__")));
          isCoroutine =
              e->getType()->is(getMangledClass("std.internal.core", "Coroutine")) ||
              e->getType()->is(getMangledClass("std.asyncio", "Future")) ||
              e->getType()->is(getMangledClass("std.asyncio", "Task")) ||
              e->getType()->is(getMangledClass("std.internal.core", "Generator"));
          if (!isCoroutine) {
            E(Error::EXPECTED_TYPE, expr, "awaitable");
          } else {
            expr->expr = e;
            expr->transformed = true;
          }
        } else {
          E(Error::EXPECTED_TYPE, expr, "awaitable");
        }
      }
    }
  }

  if (expr->getExpr()->getType()->getClass())
    unify(expr->getType(), extractClassGeneric(expr->getExpr()->getType()));

  if (expr->getExpr()->isDone())
    expr->setDone();
}

/// Typecheck return statements. Empty return is transformed to `return NoneType()`.
/// Also partialize functions if they are being returned.
/// See @c wrapExpr for more details.
namespace {
/// NES: counts the `return value` statements of a function body, without nested functions and classes.
struct NesReturnCounter : public ReplacingCallbackASTVisitor {
  int count = 0;
  Expr *transform(Expr *e) override { return e; }
  Stmt *transform(Stmt *s) override {
    if (!s || cast<FunctionStmt>(s) || cast<ClassStmt>(s))
      return s;
    if (auto r = cast<ReturnStmt>(s); r && r->getExpr())
      count++;
    s->accept(*this);
    return s;
  }
};
} // namespace

void TypecheckVisitor::visit(ReturnStmt *stmt) {
  if (stmt->hasAttribute(Attr::Internal)) {
    stmt->expr = transform(N<CallExpr>(
        N<IdExpr>(getMangledMethod("std.internal.core", "NoneType", "__new__"))));
    stmt->setDone();
    return;
  }

  if (!ctx->inFunction())
    E(Error::FN_OUTSIDE_ERROR, stmt, "return");
  auto isAsync = ctx->getBase()->func->isAsync();

  if (!stmt->expr && ctx->getBase()->func->hasAttribute(Attr::IsGenerator)) {
    stmt->setDone();
  } else {
    if (ctx->getBase()->func->hasAttribute(Attr::IsGenerator))
      E(Error::CUSTOM, stmt, "returning values from generators not yet supported");
    if (!stmt->expr)
      stmt->expr = N<CallExpr>(N<IdExpr>("NoneType"));
    stmt->expr = transform(stmt->getExpr());

    // In user code, a return whose value type is not known yet does not bind the return type yet: binding links the two,
    // and a later return of another type (e.g. an Optional[str] argument returned as is) then also fixes the type of this
    // value, which conflicts once the value resolves (e.g. to str). The statement is checked again in a later pass.
    if (!isAsync && stmt->getExpr()->getType()->getUnbound() &&
        ctx->getBase()->returnType->getUnbound() && inUserCode())
      return;

    // NES: union return types. In a Python function with several returns, each return records its value's type and
    // waits while the return type is open. Once every return has a type: types that fit each other (equal, one class,
    // int and float, Optional or None) go on as before; other types make the return type Union[...] of them, and each
    // return wraps its value (wrapExpr). If the iterations stall first (e.g. a recursive call), everything goes on as
    // before (bindIntReturns).
    if (!isAsync && inPythonFile() && ctx->getBase()->returnType->getUnbound() &&
        ctx->getBase()->nesReturnDecision == 0 && !ctx->getBase()->func->hasAttribute(Attr::IsGenerator)) {
      auto &base = *ctx->getBase();
      if (base.nesReturns < 0) {
        NesReturnCounter counter;
        if (auto fn = getFunction(base.name); fn && fn->origAst)
          counter.transform(fn->origAst->getSuite());
        base.nesReturns = counter.count;
      }
      if (base.nesReturns < 2 || base.bindIntReturns) {
        base.nesReturnDecision = 1;
      } else {
        auto vt = stmt->getExpr()->getType();
        if (auto st = vt->getStatic())
          vt = st->getNonStaticType();
        // A class with open generics (`Tuple[str, Optional[T]]` of `return x, None`) counts as known.
        if (vt->getClass())
          base.nesReturnTypes[stmt] = vt->shared_from_this();
        if (base.nesReturnTypes.size() < static_cast<size_t>(base.nesReturns)) {
          base.intReturnsDeferred = true;
          if (!ctx->blockLevel)
            ctx->returnEarly = true;
          return;
        }
        std::vector<types::ClassType *> distinct;
        bool simple = true;
        for (auto &[s, t] : base.nesReturnTypes) {
          auto c = t->getClass();
          if (!c || !c->canRealize() || c->is(TYPE_OPTIONAL) || c->is("NoneType") || t->getFunc() ||
              c->getUnion() || c->is("Generator") || c->is(TYPE_TYPE))
            simple = false;
          else if (std::ranges::none_of(distinct, [&](auto *d) { return d->name == c->name; }))
            distinct.push_back(c);
        }
        bool numeric = distinct.size() == 2 && std::ranges::all_of(distinct, [](auto *d) {
                         return d->is("int") || d->is("float");
                       });
        if (!simple || distinct.size() < 2 || numeric) {
          base.nesReturnDecision = 1;
        } else {
          std::vector<Expr *> members;
          for (auto *d : distinct)
            members.push_back(N<IdExpr>(realize(d)->realizedName()));
          auto u = transformType(
              N<InstantiateExpr>(N<IdExpr>(getMangledClass("std.internal.core", "Union")), members));
          unify(base.returnType.get(), extractType(u));
          base.nesReturnDecision = 2;
        }
      }
    }

    // NES: in user code, an int return waits while the return type is unbound, so that a float return elsewhere
    // (`return 1` and `return 1 - d / m`) makes the return type float and this value converts to it; inferTypes binds
    // the waiting returns when nothing else changes.
    if (!isAsync && ctx->getBase()->returnType->getUnbound() && inUserCode() &&
        !ctx->getBase()->bindIntReturns && stmt->getExpr()->getClassType() &&
        stmt->getExpr()->getClassType()->is("int")) {
      ctx->getBase()->intReturnsDeferred = true;
      // A waiting return still ends the code after it (a static `if` with a return).
      if (!ctx->blockLevel)
        ctx->returnEarly = true;
      return;
    }
    // NES: a tuple return without Optional elements waits in the same way, so that a return with an Optional element
    // (`return url, None` after `return url[:i], url[i+1:]`) sets the return type, and this tuple's elements are wrapped.
    if (!isAsync && ctx->getBase()->returnType->getUnbound() && inPythonFile() &&
        !ctx->getBase()->bindIntReturns && stmt->getExpr()->getClassType() &&
        stmt->getExpr()->getClassType()->is(TYPE_TUPLE) && stmt->getExpr()->getClassType()->canRealize()) {
      auto vt = stmt->getExpr()->getClassType();
      bool optional = false;
      for (size_t i = 0; i < vt->size(); i++)
        if (auto e = (*vt)[i]->getClass(); e && (e->is(TYPE_OPTIONAL) || e->is("NoneType")))
          optional = true;
      if (!optional && vt->size() > 0) {
        ctx->getBase()->intReturnsDeferred = true;
        if (!ctx->blockLevel)
          ctx->returnEarly = true;
        return;
      }
    }

    // A returned value whose type does not match the annotated return type T converts through `value.__as__(T)` if its
    // class (or the class in an Optional) has that method; a None in the Optional fails at run time, as when an Optional
    // is returned as its content type.
    if (!isAsync && !ctx->getBase()->returnType->getUnbound()) {
      auto returnType = ctx->getBase()->returnType->getClass();
      auto valueType = stmt->getExpr()->getClassType();
      if (returnType && valueType && returnType->canRealize() && valueType->canRealize()) {
        types::Type::Unification us;
        auto score = returnType->unify(valueType, &us);
        us.undo();
        Expr *value = stmt->getExpr();
        auto convertedType = valueType;
        if (valueType->is(TYPE_OPTIONAL)) {
          convertedType = extractClassGeneric(valueType)->getClass();
          value = N<CallExpr>(N<DotExpr>(value, "__val__"));
        }
        // An Optional[X] return type converts to X; None stays None.
        auto targetType = returnType;
        if (returnType->is(TYPE_OPTIONAL))
          targetType = extractClassGeneric(returnType)->getClass();
        // NES: also between instances of one generic class (records of dict literals: str to Optional[str] fields).
        if (score < 0 && convertedType && targetType &&
            (!targetType->is(convertedType->name) ||
             (targetType->canRealize() && convertedType->canRealize() &&
              targetType->realizedName() != convertedType->realizedName())) &&
            !findMethod(convertedType, "__as__").empty()) {
          if (valueType->is(TYPE_OPTIONAL) && returnType->is(TYPE_OPTIONAL)) {
            // `(v := value; None if v is None else Optional(v.__val__().__as__(X)))`
            auto var = getTemporaryVar("ret");
            stmt->expr = transform(N<StmtExpr>(
                N<AssignStmt>(N<IdExpr>(var), stmt->getExpr()),
                N<IfExpr>(N<BinaryExpr>(N<IdExpr>(var), "is", N<NoneExpr>()), N<NoneExpr>(),
                          N<CallExpr>(N<IdExpr>(TYPE_OPTIONAL),
                                      N<CallExpr>(N<DotExpr>(N<CallExpr>(N<DotExpr>(N<IdExpr>(var), "__val__")), "__as__"),
                                                  N<IdExpr>(targetType->realizedName()))))));
          } else {
            stmt->expr = transform(N<CallExpr>(N<DotExpr>(value, "__as__"),
                                               N<IdExpr>(targetType->realizedName())));
          }
        }
      }
    }

    // NES: a returned tuple whose element is a T where the return type has an Optional[T] (`return url, None` and later
    // `return url, rest`, CPython's urllib.parse._splitparams) wraps that element, as wrapExpr does for a single value:
    // `(t := value; (t[0], Optional(t[1])))`.
    if (!isAsync && !ctx->getBase()->returnType->getUnbound() && inPythonFile()) {
      auto rt = ctx->getBase()->returnType->getClass();
      auto vt = stmt->getExpr()->getClassType();
      if (rt && vt && rt->is(TYPE_TUPLE) && vt->is(TYPE_TUPLE) && rt->size() == vt->size() && vt->canRealize()) {
        std::vector<bool> wrap(vt->size(), false);
        bool any = false;
        for (size_t i = 0; i < vt->size(); i++) {
          auto r = (*rt)[i]->getClass();
          auto v = (*vt)[i]->getClass();
          if (r && v && r->is(TYPE_OPTIONAL) && !v->is(TYPE_OPTIONAL) && !v->is("NoneType"))
            wrap[i] = any = true;
        }
        if (any) {
          auto var = getTemporaryVar("ret");
          std::vector<Expr *> items;
          for (size_t i = 0; i < vt->size(); i++) {
            Expr *item = N<IndexExpr>(N<IdExpr>(var), N<IntExpr>(i));
            items.push_back(wrap[i] ? N<CallExpr>(N<IdExpr>(TYPE_OPTIONAL), item) : item);
          }
          stmt->expr = transform(
              N<StmtExpr>(N<AssignStmt>(N<IdExpr>(var), stmt->getExpr()), N<TupleExpr>(items)));
        }
      }
    }

    // Wrap expression to match the return type
    if (!ctx->getBase()->returnType->getUnbound())
      if (!wrapExpr(&stmt->expr, ctx->getBase()->returnType.get())) {
        return;
      }

    // Special case: partialize functions if we are returning them
    if (stmt->getExpr()->getType()->getFunc() &&
        !(ctx->getBase()->returnType->getClass() &&
          ctx->getBase()->returnType->is("Function"))) {
      stmt->expr = transform(
          N<CallExpr>(N<IdExpr>(stmt->getExpr()->getType()->getFunc()->ast->getName()),
                      N<EllipsisExpr>(EllipsisExpr::PARTIAL)));
    }

    if (!ctx->getBase()->returnType->getStaticKind() &&
        stmt->getExpr()->getType()->getStatic())
      stmt->getExpr()->setType(stmt->getExpr()
                                   ->getType()
                                   ->getStatic()
                                   ->getNonStaticType()
                                   ->shared_from_this());

    if (isAsync) {
      unify(ctx->getBase()->returnType.get(),
            instantiateType(getStdLibType("Coroutine"), {stmt->getExpr()->getType()}));
    } else {
      unify(ctx->getBase()->returnType.get(), stmt->getExpr()->getType());
    }
  }

  // If we are not within conditional block, ignore later statements in this function.
  // Useful with static if statements.
  if (!ctx->blockLevel)
    ctx->returnEarly = true;

  if (!stmt->getExpr() || stmt->getExpr()->isDone())
    stmt->setDone();
}

/// Typecheck yield statements. Empty yields assume `NoneType`.
void TypecheckVisitor::visit(YieldStmt *stmt) {
  if (!ctx->inFunction())
    E(Error::FN_OUTSIDE_ERROR, stmt, "yield");
  auto isAsync = ctx->getBase()->func->isAsync();

  stmt->expr =
      transform(stmt->getExpr() ? stmt->getExpr() : N<CallExpr>(N<IdExpr>("NoneType")));
  unify(ctx->getBase()->returnType.get(),
        instantiateType(getStdLibType(!isAsync ? "Generator" : "AsyncGenerator"),
                        {stmt->getExpr()->getType()}));

  if (stmt->getExpr()->isDone())
    stmt->setDone();
}

/// Transform `yield from` statements.
/// @example
///   `yield from a` -> `for var in a: yield var`
void TypecheckVisitor::visit(YieldFromStmt *stmt) {
  auto var = getTemporaryVar("yield");
  resultStmt = transform(
      N<ForStmt>(N<IdExpr>(var), stmt->getExpr(), N<YieldStmt>(N<IdExpr>(var))));
}

/// Process `global` statements. Remove them upon completion.
void TypecheckVisitor::visit(GlobalStmt *stmt) { resultStmt = N<SuiteStmt>(); }

/// Parse a function stub and create a corresponding generic function type.
/// Also realize built-ins and extern C functions.
void TypecheckVisitor::visit(FunctionStmt *stmt) {
  if (stmt->hasAttribute(Attr::Python)) {
    // Handle Python block
    resultStmt =
        transformPythonDefinition(stmt->getName(), stmt->items, stmt->getReturn(),
                                  stmt->getSuite()->firstInBlock());
    return;
  }
  auto origStmt = clean_clone(stmt);

  // Parse attributes
  std::vector<std::string> attributes;
  bool hasDecorators = false;
  for (auto i = stmt->decorators.size(); i-- > 0;) {
    if (!stmt->decorators[i])
      continue;
    auto [isAttr, attrName, attrRealizedName] = getDecorator(stmt->decorators[i]);
    if (!attrName.empty()) {
      if (attrName == getMangledFunc("std.internal.attributes", "test"))
        stmt->setAttribute(Attr::Test);
      else if (attrName == getMangledFunc("std.internal.attributes", "export"))
        stmt->setAttribute(Attr::Export);
      else if (attrName == getMangledFunc("std.internal.attributes", "inline"))
        stmt->setAttribute(Attr::Inline);
      else if (attrName == getMangledFunc("std.internal.attributes", "no_arg_reorder"))
        stmt->setAttribute(Attr::NoArgReorder);
      else if (attrName == getMangledFunc("std.internal.core", "overload"))
        stmt->setAttribute(Attr::Overload);

      if (!stmt->hasAttribute(Attr::FunctionAttributes))
        stmt->setAttribute(Attr::FunctionAttributes,
                           std::make_unique<ir::KeyValueAttribute>());

      std::string key = attrRealizedName;
      stmt->getAttribute<ir::KeyValueAttribute>(Attr::FunctionAttributes)
          ->attributes[attrName] = key;

      const auto &attrFn = getFunction(attrName);
      if (attrFn && attrFn->ast) {
        if (attrFn->ast->hasAttribute(Attr::Export))
          stmt->setAttribute(Attr::Export);
        if (attrFn->ast->hasAttribute(Attr::Inline))
          stmt->setAttribute(Attr::Inline);
        if (attrFn->ast->hasAttribute(Attr::NoArgReorder))
          stmt->setAttribute(Attr::NoArgReorder);
        if (attrFn->ast->hasAttribute(Attr::ForceRealize))
          stmt->setAttribute(Attr::ForceRealize);
        if (attrFn->ast->hasAttribute(Attr::FunctionAttributes)) {
          for (const auto &[k, v] :
               attrFn->ast
                   ->getAttribute<ir::KeyValueAttribute>(Attr::FunctionAttributes)
                   ->attributes)
            stmt->getAttribute<ir::KeyValueAttribute>(Attr::FunctionAttributes)
                ->attributes[k] = v;
        }
      }
      if (isAttr)
        stmt->decorators[i] = nullptr; // remove it from further consideration
    }
    if (!isAttr) {
      hasDecorators = true;
    }
  }

  bool isClassMember = ctx->inClass();
  if (stmt->hasAttribute(Attr::ForceRealize) && (!ctx->isGlobal() || isClassMember))
    E(Error::EXPECTED_TOPLEVEL, getSrcInfo(), "builtin function");

  // All overloads share the same canonical name except for the number at the
  // end (e.g., `foo.1:0`, `foo.1:1` etc.)
  std::string rootName;
  if (isClassMember) {
    // Case 1: method overload
    if (auto n = in(getClass(ctx->getBase()->name)->methods, stmt->getName()))
      rootName = *n;

    // TODO: handle static inherits and auto-generated cases
    // if (!rootName.empty() && stmt->hasAttribute(Attr::Overload)) {
    //   compilationWarning(
    //       fmt::format("function '{}' should be marked with @overload",
    //       stmt->getName()), getSrcInfo().file, getSrcInfo().line);
    // }
    if (rootName.empty() && stmt->hasAttribute(Attr::Overload)) {
      compilationWarning(fmt::format("function '{}' marked with unnecessary @overload",
                                     stmt->getName()),
                         getSrcInfo().file, getSrcInfo().line);
    }
  } else if (stmt->hasAttribute(Attr::Overload)) {
    // Case 2: function overload
    if (auto c = ctx->find(stmt->getName(), getTime())) {
      if (c->isFunc() && c->getModule() == ctx->getModule() &&
          c->getBaseName() == ctx->getBaseName()) {
        rootName = c->canonicalName;
      }
    }
  }
  if (rootName.empty())
    rootName = ctx->generateCanonicalName(stmt->getName(), true, isClassMember);
  // Append overload number to the name
  auto canonicalName = rootName;
  if (!in(ctx->cache->overloads, rootName))
    ctx->cache->overloads.insert({rootName, {}});
  canonicalName += fmt::format(":{}", getOverloads(rootName).size());
  ctx->cache->reverseIdentifierLookup[canonicalName] = stmt->getName();

  if (isClassMember) {
    // Set the enclosing class name
    stmt->setAttribute(Attr::ParentClass, ctx->getBase()->name);
    // Add the method to the class' method list
    getClass(ctx->getBase()->name)->methods[stmt->getName()] = rootName;
  }

  // Handle captures. Add additional argument to the function for every capture.
  // Make sure to account for **kwargs if present
  if (auto b = stmt->getAttribute<BindingsAttribute>(Attr::Bindings)) {
    size_t insertSize = stmt->size();
    if (!stmt->empty() && startswith(stmt->back().name, "**"))
      insertSize--;
    for (auto &[c, t] : b->captures) {
      std::string cc = "$" + c;
      if (auto v = ctx->find(c, getTime())) {
        if (t != BindingsAttribute::CaptureType::Global && !v->isGlobal()) {
          bool parentClassGeneric =
              ctx->bases.back().isType() && ctx->bases.back().name == v->getBaseName();
          if (v->isGeneric() && parentClassGeneric) {
            stmt->setAttribute(Attr::Method);
          }
          if (!v->isGeneric() || (v->getStaticKind() && !parentClassGeneric)) {
            if (!v->isFunc()) {
              if (v->isType()) {
                stmt->items.insert(stmt->items.begin() + insertSize++,
                                   Param(cc, N<IdExpr>(TYPE_TYPE)));
              } else if (auto si = v->getStaticKind()) {
                stmt->items.insert(
                    stmt->items.begin() + insertSize++,
                    Param(cc, N<IndexExpr>(N<IdExpr>("Literal"),
                                           N<IdExpr>(Type::stringFromLiteral(si)))));
              } else {
                stmt->items.insert(stmt->items.begin() + insertSize++, Param(cc));
              }
            } else {
              // Local function is captured. Just note its canonical name and add it to
              // the context during realization.
              b->localRenames[c] = v->getName();
            }
          }
          continue;
        }
      }
      if ((c == stmt->getName() && hasDecorators) /* decorated recursive fns */ ||
          in(ctx->globalShadows, c)) {
        // log("-> {} / {}", stmt->getName(), c);
        stmt->items.insert(stmt->items.begin() + insertSize++, Param(cc));
      }
    }
  }

  std::vector<Param> args;
  Stmt *suite = nullptr;
  Expr *ret = nullptr;
  std::vector<ClassType::Generic> explicits;
  std::shared_ptr<types::ClassType> baseType = nullptr;
  bool isGlobal = ctx->isGlobal();

  // NES: in a Python file, `Any` and `AnyStr` annotations (also `| None` and Optional[...] of them) mean "any type", as
  // the parameter or result would be without an annotation. Codon's Any is a box without the value's methods, so such
  // an annotation is removed and the type is inferred.
  if (endswith(ctx->moduleName.path, ".py")) {
    std::function<bool(Expr *)> isAny = [&](Expr *e) -> bool {
      if (auto id = cast<IdExpr>(e)) {
        auto v = id->getValue();
        return v == "Any" || v == "AnyStr" || endswith(v, ".Any") || endswith(v, ".AnyStr");
      }
      if (auto b = cast<BinaryExpr>(e))
        return b->getOp() == "|" && (isAny(b->getLhs()) || cast<NoneExpr>(b->getLhs())) &&
               (isAny(b->getRhs()) || cast<NoneExpr>(b->getRhs())) && (isAny(b->getLhs()) || isAny(b->getRhs()));
      if (auto ix = cast<IndexExpr>(e))
        return isId(ix->getExpr(), "Optional") && isAny(ix->getIndex());
      return false;
    };
    for (auto &a : *stmt)
      if (a.isValue() && a.getType() && isAny(a.getType()))
        a.type = nullptr;
    if (stmt->getReturn() && isAny(stmt->getReturn()))
      stmt->ret = nullptr;
  }

  {
    // Set up the base
    TypeContext::BaseGuard br(ctx.get(), canonicalName);
    ctx->getBase()->func = stmt;

    // Parse arguments and add them to the context
    for (auto &a : *stmt) {
      auto [stars, varName] = a.getNameWithStars();
      auto name = ctx->generateCanonicalName(varName);

      // Mark as method if the first argument is self
      if (isClassMember && stmt->hasAttribute(Attr::HasSelf) && a.getName() == "self")
        stmt->setAttribute(Attr::Method);

      // Handle default values
      auto defaultValue = a.getDefault();
      if (match(defaultValue, MOr(M<NoneExpr>(), M<IntExpr>(), M<BoolExpr>(),
                                  M<FloatExpr>(), M<IdExpr>(), M<StringExpr>()))) {
        // Special case: all simple types and Nones are handled at call site
        // (as they are not mutable).
        if (match(defaultValue, M<NoneExpr>())) {
          if (match(a.getType(), M<IdExpr>(MOr(TYPE_TYPE, TRAIT_TYPE)))) {
            // Special case: `arg: type = None` -> `arg: type = NoneType`
            defaultValue = N<IdExpr>("NoneType");
          } else {
            ; // Do nothing. NoneExpr will be handled later (we don't want it
              // to be converted to Optional call yet.)
          }
        } else {
          defaultValue = transform(defaultValue);
        }
      } else if (defaultValue) {
        if (!a.isValue()) {
          // Special case: generic defaults are evaluated as-is!
          defaultValue = transform(defaultValue);
        } else {
          auto defName = fmt::format(".default.{}.{}", canonicalName, a.getName());
          auto nctx = std::make_shared<TypeContext>(ctx->cache);
          *nctx = *ctx;
          nctx->bases.pop_back();
          if (isClassMember) // class variable; go to the global context!
            nctx->bases.erase(nctx->bases.begin() + 1, nctx->bases.end());
          auto tv = TypecheckVisitor(nctx);
          auto as = N<AssignStmt>(N<IdExpr>(defName), defaultValue,
                                  a.isValue() ? nullptr : a.getType());
          if (isClassMember) {
            preamble->addStmt(
                tv.transform(N<AssignStmt>(N<IdExpr>(defName), nullptr, nullptr)));
            registerGlobal(defName);
            as->setUpdate();
          } else if (isGlobal) {
            registerGlobal(defName);
          }
          auto das = tv.transform(as);
          prependStmts->push_back(das);
          // Default unbounds must be allowed to pass through
          // to support cases such as `a = []`
          auto f = ctx->forceFind(defName);
          for (auto &u : f->getType()->getUnbounds(false)) {
            // log("pass-through: {} / {}", stmt->getName(), u->debugString(2));
            u->getUnbound()->passThrough = true;
            stmt->setAttribute(Attr::AllowPassThrough);
          }
          defaultValue = tv.transform(N<IdExpr>(defName));
        }
      }
      args.emplace_back(std::string(stars, '*') + name, a.getType(), defaultValue,
                        a.status);

      // Add generics to the context
      if (!a.isValue()) {
        // Generic and static types
        auto generic = instantiateUnbound();
        auto typId = generic->getLink()->id;
        generic->genericName = varName;
        auto defType = transform(clone(a.getDefault()));
        if (auto st = getStaticGeneric(a.getType())) {
          auto val = ctx->addVar(varName, name, generic);
          val->generic = true;
          generic->staticKind = st;
          if (defType)
            generic->defaultType = extractType(defType)->shared_from_this();
        } else {
          if (match(a.getType(), M<InstantiateExpr>(M<IdExpr>(TRAIT_TYPE), M_))) {
            // Parse TraitVar
            auto l = transformType(cast<InstantiateExpr>(a.getType())->front(), true)
                         ->getType();
            if (l->getLink() && l->getLink()->trait)
              generic->getLink()->trait = l->getLink()->trait;
            else
              generic->getLink()->trait =
                  std::make_shared<types::TypeTrait>(l->shared_from_this());
          }
          auto val = ctx->addType(varName, name, generic);
          val->generic = true;
          if (defType)
            generic->defaultType = extractType(defType)->shared_from_this();
        }
        auto g = generic->generalize(ctx->typecheckLevel);
        if (startswith(varName, "$"))
          varName = varName.substr(1);
        explicits.emplace_back(name, g, typId, g->getStaticKind());
      }
    }

    // Prepare list of all generic types
    ClassType *parentClass = nullptr;
    if (isClassMember && stmt->hasAttribute(Attr::Method)) {
      // Get class generics (e.g., T for `class Cls[T]: def foo:`)
      auto aa = stmt->getAttribute<ir::StringValueAttribute>(Attr::ParentClass);
      parentClass = extractClassType(aa->value);
    }
    // Add function generics
    std::vector<TypePtr> generics;
    generics.reserve(explicits.size());
    for (const auto &i : explicits)
      generics.emplace_back(extractType(i.name)->shared_from_this());

    // Handle function arguments
    // Base type: `Function[[args,...], ret]`
    baseType = getFuncTypeBase(stmt->size() - explicits.size());
    ctx->typecheckLevel++;

    // Parse arguments to the context. Needs to be done after adding generics
    // to support cases like `foo(a: T, T: type)`
    for (auto &a : args) {
      a.type = transformType(a.getType(), true);
    }

    // Unify base type generics with argument types. Add non-generic arguments to the
    // context. Delayed to prevent cases like `def foo(a, b=a)`
    auto argType = extractClassGeneric(baseType.get())->getClass();
    for (int ai = 0, aj = 0; ai < stmt->size(); ai++) {
      if (!(*stmt)[ai].isValue())
        continue;
      auto [_, canName] = (*stmt)[ai].getNameWithStars();
      if (!(*stmt)[ai].getType()) {
        if (parentClass && ai == 0 && (*stmt)[ai].getName() == "self") {
          // Special case: self in methods
          auto *st = unify(extractClassGeneric(argType, aj), parentClass);
          if (getClass(parentClass->name)->ast->hasAttribute(Attr::ClassDeduce) &&
              stmt->hasAttribute(Attr::ClassDeduce) && stmt->getName() == "__init__") {
            for (auto &u : st->getUnbounds(true)) {
              stmt->setAttribute(Attr::AllowPassThrough);
              // log("pass-through: {}.__init__ / {}", parentClass->name,
              //     u->debugString(2));
              u->getLink()->passThrough = true;
            }
          }
        } else {
          generics.push_back(extractClassGeneric(argType, aj)->shared_from_this());
        }
      } else if (startswith((*stmt)[ai].getName(), "*")) {
        // Special case: `*args: type` and `**kwargs: type`. Do not add this type to the
        // signature (as the real type is `Tuple[type, ...]`); it will be used during
        // call typechecking
        generics.push_back(extractClassGeneric(argType, aj)->shared_from_this());
      } else {
        unify(extractClassGeneric(argType, aj),
              extractType(transformType((*stmt)[ai].getType(), true)));
      }
      aj++;
    }

    // NES: in a Python file, a function annotated `-> int` can return a float (`return total / count`): CPython does not
    // enforce the annotation. The annotation is ignored and the return type is inferred from the returns (int and float
    // returns give float).
    if (stmt->getReturn() && stmt->getSuite() && endswith(ctx->moduleName.path, ".py") &&
        isId(stmt->getReturn(), "int"))
      stmt->ret = nullptr;

    // In user code, a function annotated -> T whose body returns None returns Optional[T]: CPython does not enforce the
    // annotation, so such a function returns None as well.
    if (stmt->getReturn() && stmt->getSuite() && inUserCode() &&
        returnKinds(stmt->getSuite()).first) {
      auto annotation = stmt->getReturn();
      auto index = cast<IndexExpr>(annotation);
      bool optional = (index && isId(index->getExpr(), "Optional")) || isId(annotation, "None") ||
                      isId(annotation, "NoneType") || isId(annotation, "Optional");
      if (!optional)
        stmt->ret = N<IndexExpr>(N<IdExpr>("Optional"), annotation);
    }

    // Parse the return type
    ret = transformType(stmt->getReturn(), true);
    auto retType = extractClassGeneric(baseType.get(), 1);
    if (ret) {
      // Fix for functions returning Literal types
      if (auto st = getStaticGeneric(ret))
        baseType->generics[1].staticKind = st;

      unify(retType, extractType(ret));
      if (isId(ret, "Union"))
        extractClassGeneric(retType)->getUnbound()->kind = LinkType::Generic;
    } else {
      generics.push_back(unify(retType, instantiateUnbound())->shared_from_this());
    }
    ctx->typecheckLevel--;

    // Generalize generics and remove them from the context
    for (const auto &g : generics) {
      for (auto &u : g->getUnbounds(false))
        if (u->getUnbound()) {
          u->getUnbound()->kind = LinkType::Generic;
        }
    }

    // Parse function body
    if (!stmt->hasAttribute(Attr::Internal) && !stmt->hasAttribute(Attr::C)) {
      if (stmt->hasAttribute(Attr::LLVM)) {
        suite = transformLLVMDefinition(stmt->getSuite()->firstInBlock());
      } else if (stmt->hasAttribute(Attr::C)) {
        // Do nothing
      } else {
        suite = clone(stmt->getSuite());
      }
    }
  }
  stmt->setAttribute(Attr::Module, ctx->moduleName.path);

  // Make function AST and cache it for later realization
  auto f = N<FunctionStmt>(canonicalName, ret, args, suite, std::vector<Expr *>{},
                           stmt->isAsync());
  f->cloneAttributesFrom(stmt);
  auto &fn = ctx->cache->functions[canonicalName] =
      Cache::Function{ctx->getModulePath(),
                      rootName,
                      f,
                      nullptr,
                      origStmt,
                      ctx->getModule().empty() && ctx->isGlobal()};
  f->setDone();
  auto aa = stmt->getAttribute<ir::StringValueAttribute>(Attr::ParentClass);
  auto parentClass = aa ? extractClassType(aa->value) : nullptr;

  // Construct the type
  auto funcTyp = std::make_shared<types::FuncType>(baseType.get(), fn.ast, explicits);
  funcTyp->setSrcInfo(getSrcInfo());
  if (isClassMember && stmt->hasAttribute(Attr::Method)) {
    funcTyp->funcParent = parentClass->shared_from_this();
  }
  funcTyp = std::static_pointer_cast<types::FuncType>(
      funcTyp->generalize(ctx->typecheckLevel));
  fn.type = funcTyp;

  auto &overloads = ctx->cache->overloads[rootName];
  if (rootName == "Tuple.__new__") {
    overloads.insert(std::ranges::upper_bound(
                         overloads, canonicalName,
                         [&](const auto &a, const auto &b) {
                           return getFunction(a)->getType()->funcGenerics.size() <
                                  getFunction(b)->getType()->funcGenerics.size();
                         }),
                     canonicalName);
  } else {
    overloads.push_back(canonicalName);
  }

  auto val = ctx->addFunc(stmt->name, rootName, funcTyp);
  // val->time = getTime();
  ctx->addFunc(canonicalName, canonicalName, funcTyp);
  if (stmt->hasAttribute(Attr::Overload) || isClassMember) {
    ctx->remove(stmt->name); // first overload will handle it!
  }

  // Special method handling
  if (isClassMember) {
    auto m = getClassMethod(parentClass, getUnmangledName(canonicalName));
    bool found = false;
    for (auto &i : getOverloads(m))
      if (i == canonicalName) {
        getFunction(i)->type = funcTyp;
        found = true;
        break;
      }
    seqassert(found, "cannot find matching class method for {}", canonicalName);
  } else {
    // Hack so that we can later use same helpers for class overloads
    getClass(VAR_CLASS_TOPLEVEL)->methods[stmt->getName()] = rootName;
  }

  // Ensure that functions with @C, @force_realize, and @export attributes can be
  // realized
  if (stmt->hasAttribute(Attr::ForceRealize) || stmt->hasAttribute(Attr::Export) ||
      (stmt->hasAttribute(Attr::C) && !stmt->hasAttribute(Attr::CVarArg))) {
    if (!funcTyp->canRealize())
      E(Error::FN_REALIZE_BUILTIN, stmt);
  }

  // Expression to be used if function binding is modified by captures or decorators
  Expr *finalExpr = nullptr;
  // Parse remaining decorators
  for (auto i = stmt->decorators.size(); i-- > 0;) {
    if (stmt->decorators[i]) {
      // Replace each decorator with `decorator(finalExpr)` in the reverse order
      finalExpr = N<CallExpr>(stmt->decorators[i],
                              finalExpr ? finalExpr : N<IdExpr>(canonicalName));
    }
  }
  if (finalExpr) {
    auto a = N<AssignStmt>(N<IdExpr>(stmt->getName()), finalExpr);
    if (isClassMember) { // class method decorator
      auto nctx = std::make_shared<TypeContext>(ctx->cache);
      *nctx = *ctx;
      nctx->bases.pop_back();
      nctx->bases.erase(nctx->bases.begin() + 1, nctx->bases.end()); // global context
      auto tv = TypecheckVisitor(nctx);

      auto defName = ctx->generateCanonicalName(stmt->getName());
      preamble->addStmt(
          tv.transform(N<AssignStmt>(N<IdExpr>(defName), nullptr, nullptr)));
      registerGlobal(defName);
      a->setUpdate();

      cast<IdExpr>(a->getLhs())->value = defName;
      std::vector<CallArg> args;
      for (auto arg : *stmt) {
        if (startswith(arg.name, "**"))
          args.push_back(N<KeywordStarExpr>(N<IdExpr>(arg.name)));
        else if (startswith(arg.name, "*"))
          args.push_back(N<StarExpr>(N<IdExpr>(arg.name)));
        else
          args.push_back(N<IdExpr>(arg.name));
      }
      Stmt *newFunc = N<FunctionStmt>(
          stmt->getName(), clone(stmt->getReturn()), clone(stmt->items),
          N<SuiteStmt>(N<ReturnStmt>(N<CallExpr>(N<IdExpr>(defName), args))),
          std::vector<Expr *>{}, stmt->isAsync());
      newFunc = transform(newFunc);
      resultStmt = N<SuiteStmt>(f, N<SuiteStmt>(transform(a), newFunc));
    } else {
      resultStmt = N<SuiteStmt>(f, transform(a));
    }
  } else {
    resultStmt = f;
  }
}

/// Transform Python code blocks.
/// @example
///   ```@python
///      def foo(x: int, y) -> int:
///        [code]
///   ``` -> ```
///      pyobj._exec("def foo(x, y): [code]")
///      from python import __main__.foo(int, _) -> int
///   ```
Stmt *TypecheckVisitor::transformPythonDefinition(const std::string &name,
                                                  const std::vector<Param> &args,
                                                  Expr *ret, Stmt *codeStmt) {
  seqassert(codeStmt && cast<ExprStmt>(codeStmt) &&
                cast<StringExpr>(cast<ExprStmt>(codeStmt)->getExpr()),
            "invalid Python definition");

  auto code = cast<StringExpr>(cast<ExprStmt>(codeStmt)->getExpr())->getValue();
  std::vector<std::string> pyargs;
  pyargs.reserve(args.size());
  for (const auto &a : args)
    pyargs.emplace_back(a.getName());
  code = fmt::format("def {}({}):\n{}\n", name, join(pyargs, ", "), code);
  return transform(N<SuiteStmt>(
      N<ExprStmt>(
          N<CallExpr>(N<DotExpr>(N<IdExpr>("pyobj"), "_exec"), N<StringExpr>(code))),
      N<ImportStmt>(N<IdExpr>("python"), N<DotExpr>(N<IdExpr>("__main__"), name),
                    clone(args), ret ? clone(ret) : N<IdExpr>("pyobj"))));
}

/// Transform LLVM functions.
/// @example
///   ```@llvm
///      def foo(x: int) -> float:
///        [code]
///   ``` -> ```
///      def foo(x: int) -> float:
///        StringExpr("[code]")
///        SuiteStmt(referenced_types)
///   ```
/// As LLVM code can reference types and static expressions in `{=expr}` blocks,
/// all block expression will be stored in the `referenced_types` suite.
/// "[code]" is transformed accordingly: each `{=expr}` block will
/// be replaced with `{}` so that @c fmt::format can fill the gaps.
/// Note that any brace (`{` or `}`) that is not part of a block is
/// escaped (e.g. `{` -> `{{` and `}` -> `}}`) so that @c fmt::format can process them.
Stmt *TypecheckVisitor::transformLLVMDefinition(Stmt *codeStmt) {
  StringExpr *codeExpr;
  auto m = match(codeStmt, M<ExprStmt>(MVar<StringExpr>(codeExpr)));
  seqassert(m, "invalid LLVM definition");
  auto code = codeExpr->getValue();
  /// Remove docstring (if any)
  size_t start = 0;
  while (start < code.size() && std::isspace(code[start]))
    start++;
  if (startswith(code.substr(start), "\"\"\"")) {
    start += 3;
    bool found = false;
    while (start < code.size() - 2) {
      if (code[start] == '"' && code[start + 1] == '"' && code[start + 2] == '"') {
        found = true;
        start += 3;
        break;
      }
      start++;
    }
    if (found) {
      code = code.substr(start);
    }
  }

  std::vector<Stmt *> items;
  std::string finalCode;
  items.push_back(nullptr);

  // Parse LLVM code and look for expression blocks that start with `{=`
  int braceCount = 0, braceStart = 0;
  for (int i = 0; i < code.size(); i++) {
    if (i < code.size() - 1 && code[i] == '\\' && code[i + 1] == '\n') {
      code[i] = code[i + 1] = ' ';
    }
    if (i < code.size() - 1 && code[i] == '{' && code[i + 1] == '=') {
      if (braceStart <= i)
        finalCode += escapeFStringBraces(code, braceStart, i - braceStart) + '{';
      if (!braceCount) {
        braceStart = i + 2;
        braceCount++;
      } else {
        E(Error::FN_BAD_LLVM, getSrcInfo());
      }
    } else if (braceCount && code[i] == '}') {
      braceCount--;
      std::string exprCode = code.substr(braceStart, i - braceStart);
      auto offset = getSrcInfo();
      offset.col += i;
      auto exprOrErr = parseExpr(ctx->cache, exprCode, offset);
      if (!exprOrErr)
        throw exc::ParserException(exprOrErr.takeError());
      auto expr = exprOrErr->first;
      items.push_back(N<ExprStmt>(expr));
      braceStart = i + 1;
      finalCode += '}';
    }
  }
  if (braceCount)
    E(Error::FN_BAD_LLVM, getSrcInfo());
  if (braceStart != code.size())
    finalCode += escapeFStringBraces(code, braceStart,
                                     static_cast<int>(code.size()) - braceStart);
  items[0] = N<ExprStmt>(N<StringExpr>(finalCode));
  return N<SuiteStmt>(items);
}

/// Fetch a decorator canonical name. The first pair member indicates if a decorator is
/// actually an attribute (a function with `@__attribute__`).
std::tuple<bool, std::string, std::string> TypecheckVisitor::getDecorator(Expr *e) {
  auto dt = transform(clone(e));
  dt = getHeadExpr(dt);
  if (auto id = cast<IdExpr>(cast<CallExpr>(dt) ? cast<CallExpr>(dt)->getExpr() : dt)) {
    auto ci = ctx->find(id->getValue(), getTime());
    if (ci && ci->isFunc()) {
      auto fn = ci->getType()->getFunc()->ast->getName();
      auto f = getFunction(fn);
      if (!f) {
        if (auto o = in(ctx->cache->overloads, fn)) {
          if (o->size() == 1)
            f = getFunction(o->front());
        }
      }
      // Special case: Id to Call
      if (f->ast->hasAttribute(Attr::Attribute) && cast<IdExpr>(dt))
        dt = transform(N<CallExpr>(dt));
      if (f)
        return {f->ast->hasAttribute(Attr::Attribute), fn,
                dt->isDone() ? id->getValue() : ""};
    }
  }
  return {false, "", ""};
}

/// Generate and return `Function[Tuple[args...], ret]` type
std::shared_ptr<ClassType> TypecheckVisitor::getFuncTypeBase(size_t nargs) {
  auto baseType = instantiateType(getStdLibType("Function"));
  unify(extractClassGeneric(baseType->getClass()),
        instantiateType(generateTuple(nargs, false)));
  return std::static_pointer_cast<types::ClassType>(baseType);
}

} // namespace codon::ast
