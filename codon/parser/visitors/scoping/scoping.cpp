// Copyright (C) 2022-2023 Exaloop Inc. <https://exaloop.io>

#include <functional>
#include <memory>
#include <utility>
#include <vector>

#include "codon/parser/ast.h"
#include "codon/parser/common.h"
#include "codon/parser/match.h"
#include "codon/parser/peg/peg.h"
#include "codon/parser/visitors/scoping/scoping.h"
#include "codon/parser/visitors/typecheck/typecheck.h"

#define CHECK(x)                                                                       \
  {                                                                                    \
    if (!(x))                                                                          \
      return;                                                                          \
  }
#define STOP_ERROR(...)                                                                \
  do {                                                                                 \
    addError(__VA_ARGS__);                                                             \
    return;                                                                            \
  } while (0)

using namespace codon::error;
using namespace codon::matcher;

namespace codon::ast {

llvm::Error
ScopingVisitor::apply(Cache *cache, Stmt *s,
                      std::unordered_map<std::string, size_t> *globalShadows) {
  auto c = std::make_shared<ScopingVisitor::Context>();
  c->cache = cache;
  c->functionScope = nullptr;
  ScopingVisitor v;
  v.ctx = c;

  ConditionalBlock cb(c.get(), s, 0);
  v.nesConditionalDefs(s);
  if (!v.transform(s))
    return llvm::make_error<ParserErrorInfo>(v.errors);
  if (v.hasErrors())
    return llvm::make_error<ParserErrorInfo>(v.errors);
  v.processChildCaptures();

  /// Count number of shadowed names to know which names change or not later on
  if (globalShadows) {
    for (auto &[u, v] : c->map) {
      size_t i = 0;
      for (auto &ii : v)
        if (!ii.ignore)
          i++;
      if (i > 1)
        (*globalShadows)[u] = i;
    }
  }

  // LOG("-> {}", s->toString(2));
  return llvm::Error::success();
}

bool ScopingVisitor::transform(Expr *expr) {
  if (!canContinue())
    return false;

  ScopingVisitor v(*this);
  if (expr) {
    v.setSrcInfo(expr->getSrcInfo());
    expr->accept(v);
    if (v.hasErrors())
      errors.append(v.errors);
    if (!canContinue())
      return false;
  }
  return true;
}

bool ScopingVisitor::transform(Stmt *stmt) {
  if (!canContinue())
    return false;

  ScopingVisitor v(*this);
  if (stmt) {
    v.setSrcInfo(stmt->getSrcInfo());
    stmt->setAttribute(Attr::ExprTime, ++ctx->time);
    stmt->accept(v);
    if (v.hasErrors())
      errors.append(v.errors);
    if (!canContinue())
      return false;
  }
  return true;
}

bool ScopingVisitor::transformScope(Expr *e) {
  if (e) {
    ConditionalBlock c(ctx.get(), nullptr);
    return transform(e);
  }
  return true;
}

bool ScopingVisitor::transformScope(Stmt *s) {
  if (s) {
    ConditionalBlock c(ctx.get(), s);
    return transform(s);
  }
  return true;
}

bool ScopingVisitor::transformAdding(Expr *e, ASTNode *root) {
  if (cast<IndexExpr>(e)) {
    return transform(e);
  } else if (auto de = cast<DotExpr>(e)) {
    if (!transform(e))
      return false;
    if (!ctx->classDeduce.first.empty() &&
        match(de->getExpr(), M<IdExpr>(ctx->classDeduce.first)))
      ctx->classDeduce.second.insert(de->getMember());
    return true;
  } else if (cast<ListExpr>(e) || cast<TupleExpr>(e) || cast<IdExpr>(e)) {
    // NES: `self.a, self.b = ...` in __init__ also declares the fields a and b.
    if (!ctx->classDeduce.first.empty()) {
      std::function<void(Expr *)> collect = [&](Expr *x) {
        if (auto d = cast<DotExpr>(x)) {
          if (match(d->getExpr(), M<IdExpr>(ctx->classDeduce.first)))
            ctx->classDeduce.second.insert(d->getMember());
        } else if (auto t = cast<TupleExpr>(x)) {
          for (auto *i : *t)
            collect(i);
        } else if (auto l = cast<ListExpr>(x)) {
          for (auto *i : *l)
            collect(i);
        } else if (auto st = cast<StarExpr>(x)) {
          collect(st->getExpr());
        }
      };
      collect(e);
    }
    SetInScope s1(&(ctx->adding), true);
    SetInScope s2(&(ctx->root), root);
    return transform(e);
  } else {
    seqassert(e, "bad call to transformAdding");
    addError(Error::ASSIGN_INVALID, e);
    return false;
  }
}

void ScopingVisitor::visit(IdExpr *expr) {
  if (ctx->adding)
    ctx->root = expr;
  if (ctx->adding && ctx->tempScope)
    ctx->renames.back()[expr->getValue()] =
        ctx->cache->getTemporaryVar(expr->getValue());
  for (size_t i = ctx->renames.size(); i-- > 0;)
    if (auto v = in(ctx->renames[i], expr->getValue())) {
      expr->setValue(*v);
      break;
    }
  if (visitName(expr->getValue(), ctx->adding, ctx->root, expr->getSrcInfo()))
    expr->setAttribute(Attr::ExprDominatedUndefCheck);
}

void ScopingVisitor::visit(DotExpr *expr) {
  SetInScope s(&(ctx->adding), false); // to handle a.x, y = b
  CallbackASTVisitor<bool, bool>::visit(expr);
}

void ScopingVisitor::visit(IndexExpr *expr) {
  SetInScope s(&(ctx->adding), false); // to handle a[x], y = b
  CallbackASTVisitor<bool, bool>::visit(expr);
}

void ScopingVisitor::visit(StringExpr *expr) {
  std::vector<StringExpr::String> exprs;
  for (auto &p : *expr) {
    if (p.prefix == "f" || p.prefix == "F") {
      /// Transform an F-string
      auto fstr = unpackFString(p.value);
      if (!canContinue())
        return;
      for (auto pf : fstr) {
        if (pf.prefix.empty() && !exprs.empty() && exprs.back().prefix.empty()) {
          exprs.back().value += pf.value;
        } else {
          exprs.emplace_back(pf);
        }
      }
    } else if (!p.prefix.empty()) {
      exprs.emplace_back(p);
    } else if (!exprs.empty() && exprs.back().prefix.empty()) {
      exprs.back().value += p.value;
    } else {
      exprs.emplace_back(p);
    }
  }
  expr->strings = exprs;
}

/// Split a Python-like f-string into a list:
///   `f"foo {x+1} bar"` -> `("foo ", str(x+1), " bar")
/// Supports "{x=}" specifier (that prints the raw expression as well):
///   `f"{x+1=}"` -> `("x+1=", str(x+1))`
std::vector<StringExpr::String>
ScopingVisitor::unpackFString(const std::string &value) {
  // Strings to be concatenated
  std::vector<StringExpr::String> items;
  int braceCount = 0, braceStart = 0;
  for (int i = 0; i < value.size(); i++) {
    if (value[i] == '{') {
      if (braceStart < i)
        items.emplace_back(value.substr(braceStart, i - braceStart));
      if (!braceCount)
        braceStart = i + 1;
      braceCount++;
    } else if (value[i] == '}') {
      braceCount--;
      if (!braceCount) {
        std::string code = value.substr(braceStart, i - braceStart);

        auto offset = getSrcInfo();
        offset.col += i;
        items.emplace_back(code, "#f");
        items.back().setSrcInfo(offset);

        auto val = parseExpr(ctx->cache, code, offset);
        if (!val) {
          addError(val.takeError());
        } else {
          items.back().expr = val->first;
          if (!transform(items.back().expr))
            return items;
          items.back().format = val->second;
        }
      }
      braceStart = i + 1;
    }
  }
  if (braceCount > 0)
    addError(Error::STR_FSTRING_BALANCE_EXTRA, getSrcInfo());
  else if (braceCount < 0)
    addError(Error::STR_FSTRING_BALANCE_MISSING, getSrcInfo());
  if (braceStart != value.size())
    items.emplace_back(value.substr(braceStart, value.size() - braceStart));
  return items;
}

void ScopingVisitor::visit(GeneratorExpr *expr) {
  SetInScope s(&(ctx->tempScope), true);
  ctx->renames.emplace_back();
  CHECK(transform(expr->getFinalSuite()));
  ctx->renames.pop_back();
}

void ScopingVisitor::visit(IfExpr *expr) {
  CHECK(transform(expr->getCond()));
  CHECK(transformScope(expr->getIf()));
  CHECK(transformScope(expr->getElse()));
}

void ScopingVisitor::visit(BinaryExpr *expr) {
  CHECK(transform(expr->getLhs()));
  if (expr->getOp() == "&&" || expr->getOp() == "||") {
    CHECK(transformScope(expr->getRhs()));
  } else {
    CHECK(transform(expr->getRhs()));
  }
}

void ScopingVisitor::visit(AssignExpr *expr) {
  seqassert(cast<IdExpr>(expr->getVar()),
            "only simple assignment expression are supported");

  SetInScope s(&(ctx->tempScope), false);
  CHECK(transform(expr->getExpr()));
  CHECK(transformAdding(expr->getVar(), expr));
}

void ScopingVisitor::visit(LambdaExpr *expr) {
  auto c = std::make_shared<ScopingVisitor::Context>();
  c->cache = ctx->cache;
  FunctionStmt f("lambda", nullptr, {}, nullptr);
  c->functionScope = &f;
  c->renames = ctx->renames;
  ScopingVisitor v;
  c->scope.emplace_back(0, nullptr);
  v.ctx = c;
  for (const auto &a : *expr) {
    auto [_, n] = a.getNameWithStars();
    v.visitName(n, true, expr, a.getSrcInfo());
    if (a.defaultValue)
      CHECK(transform(a.defaultValue));
  }
  c->scope.pop_back();

  SuiteStmt s;
  c->scope.emplace_back(0, &s);
  v.transform(expr->getExpr());
  v.processChildCaptures();
  c->scope.pop_back();
  if (v.hasErrors())
    errors.append(v.errors);
  if (!canContinue())
    return;

  auto b = std::make_unique<BindingsAttribute>();
  b->captures = c->captures;
  for (const auto &n : c->captures)
    ctx->childCaptures.insert(n);
  for (auto &[u, v] : c->map)
    b->bindings[u] = {u, v.size()};
  expr->setAttribute(Attr::Bindings, std::move(b));
}

void ScopingVisitor::visit(AssignStmt *stmt) {
  CHECK(transform(stmt->getRhs()));
  CHECK(transform(stmt->getTypeExpr()));
  CHECK(transformAdding(stmt->getLhs(), stmt));
}

void ScopingVisitor::visit(IfStmt *stmt) {
  CHECK(transform(stmt->getCond()));
  CHECK(transformScope(stmt->getIf()));
  CHECK(transformScope(stmt->getElse()));
}

void ScopingVisitor::visit(MatchStmt *stmt) {
  CHECK(transform(stmt->getExpr()));
  for (auto &m : *stmt) {
    CHECK(transform(m.getPattern()));
    CHECK(transform(m.getGuard()));
    CHECK(transformScope(m.getSuite()));
  }
}

void ScopingVisitor::visit(WhileStmt *stmt) {
  std::unordered_set<std::string> seen;
  {
    ConditionalBlock c(ctx.get(), stmt->getSuite());
    ctx->scope.back().seenVars = std::make_unique<std::unordered_set<std::string>>();
    CHECK(transform(stmt->getCond()));
    CHECK(transform(stmt->getSuite()));
    seen = *(ctx->scope.back().seenVars);
  }
  for (auto &var : seen) {
    findDominatingBinding(var);
  }

  CHECK(transformScope(stmt->getElse()));
}

void ScopingVisitor::visit(ForStmt *stmt) {
  CHECK(transform(stmt->getIter()));
  CHECK(transform(stmt->getDecorator()));
  for (auto &a : stmt->ompArgs)
    CHECK(transform(a.value));

  std::unordered_set<std::string> seen, seenDef;
  {
    ConditionalBlock c(ctx.get(), stmt->getSuite());

    ctx->scope.back().seenVars = std::make_unique<std::unordered_set<std::string>>();
    CHECK(transformAdding(stmt->getVar(), stmt));
    seenDef = *(ctx->scope.back().seenVars);

    ctx->scope.back().seenVars = std::make_unique<std::unordered_set<std::string>>();
    CHECK(transform(stmt->getSuite()));
    seen = *(ctx->scope.back().seenVars);
  }
  for (auto &var : seen)
    if (!in(seenDef, var))
      findDominatingBinding(var);

  CHECK(transformScope(stmt->getElse()));
}

void ScopingVisitor::visit(ImportStmt *stmt) {
  // Validate
  if (stmt->getFrom()) {
    Expr *e = stmt->getFrom();
    while (auto d = cast<DotExpr>(e))
      e = d->getExpr();
    if (!isId(stmt->getFrom(), "C") && !isId(stmt->getFrom(), "python")) {
      if (!cast<IdExpr>(e))
        STOP_ERROR(Error::IMPORT_IDENTIFIER, e);
      if (!stmt->getArgs().empty())
        STOP_ERROR(Error::IMPORT_FN, stmt->getArgs().front().getSrcInfo());
      if (stmt->getReturnType())
        STOP_ERROR(Error::IMPORT_FN, stmt->getReturnType());
      if (stmt->getWhat() && !cast<IdExpr>(stmt->getWhat()))
        STOP_ERROR(Error::IMPORT_IDENTIFIER, stmt->getWhat());
    }
    if (stmt->isCVar() && !stmt->getArgs().empty())
      STOP_ERROR(Error::IMPORT_FN, stmt->getArgs().front().getSrcInfo());
  }
  if (ctx->functionScope && stmt->getWhat() && isId(stmt->getWhat(), "*"))
    STOP_ERROR(error::Error::IMPORT_STAR, stmt);

  // dylib C imports
  if (stmt->getFrom() && isId(stmt->getFrom(), "C") && cast<DotExpr>(stmt->getWhat()))
    CHECK(transform(cast<DotExpr>(stmt->getWhat())->getExpr()));

  if (stmt->getAs().empty()) {
    if (stmt->getWhat()) {
      if (!match(stmt->getWhat(), M<IdExpr>("*")))
        CHECK(transformAdding(stmt->getWhat(), stmt));
    } else {
      CHECK(transformAdding(stmt->getFrom(), stmt));
    }
  } else {
    visitName(stmt->getAs(), true, stmt, stmt->getSrcInfo());
  }
  for (const auto &a : stmt->getArgs()) {
    CHECK(transform(a.type));
    CHECK(transform(a.defaultValue));
  }
  CHECK(transform(stmt->getReturnType()));
}

void ScopingVisitor::visit(TryStmt *stmt) {
  CHECK(transformScope(stmt->getSuite()));
  for (auto *a : *stmt) {
    CHECK(transform(a->getException()));
    ConditionalBlock c(ctx.get(), a->getSuite());
    if (!a->getVar().empty()) {
      auto newName = ctx->cache->getTemporaryVar(a->getVar());
      ctx->renames.push_back({{a->getVar(), newName}});
      a->var = newName;
      visitName(a->getVar(), true, a, a->getException()->getSrcInfo());
    }
    CHECK(transform(a->getSuite()));
    if (!a->getVar().empty())
      ctx->renames.pop_back();
  }
  CHECK(transformScope(stmt->getElse()));
  CHECK(transform(stmt->getFinally()));
}

void ScopingVisitor::visit(DelStmt *stmt) { CHECK(transform(stmt->getExpr())); }

/// Process `global` statements.
void ScopingVisitor::visit(GlobalStmt *stmt) {
  if (!ctx->functionScope)
    STOP_ERROR(Error::FN_OUTSIDE_ERROR, stmt,
               stmt->isNonLocal() ? "nonlocal" : "global");
  if (in(ctx->map, stmt->getVar()) || in(ctx->captures, stmt->getVar()))
    STOP_ERROR(Error::FN_GLOBAL_ASSIGNED, stmt, stmt->getVar());

  visitName(stmt->getVar(), true, stmt, stmt->getSrcInfo());
  // No shadowing od global/nonlocal allowed
  findDominatingBinding(stmt->getVar(), /* alowShadow= */ false);
  ctx->captures[stmt->getVar()] = stmt->isNonLocal()
                                      ? BindingsAttribute::CaptureType::Nonlocal
                                      : BindingsAttribute::CaptureType::Global;
}

void ScopingVisitor::visit(YieldStmt *stmt) {
  if (ctx->functionScope)
    ctx->functionScope->setAttribute(Attr::IsGenerator);
  CHECK(transform(stmt->getExpr()));
}

void ScopingVisitor::visit(YieldExpr *expr) {
  if (ctx->functionScope)
    ctx->functionScope->setAttribute(Attr::IsGenerator);
}

/// NES: Python code defines a function of the same name on different paths:
///   if isinstance(qs, str):
///       def _unquote(s): ...
///   else:
///       def _unquote(s): ...
/// Scoping must then treat the name as a variable that each path updates, which Codon does not allow for a def
/// ("cannot bind ... to global or nonlocal name"). Each such def becomes a def of a new name and an assignment:
///   def _nes_def__unquote_1(s): ...
///   _unquote = _nes_def__unquote_1
/// The rule applies to a name with two or more defs in one scope (a function body or the module), at least one of them
/// inside a compound statement (if, loop, try, with); `@overload` defs stay as they are. A reference of the def to its
/// own name (recursion) uses the new name. The type checker drops a branch whose condition is static (`isinstance`), so
/// there the variable has one type; two live paths need functions of the same type.
namespace {
struct NesRenameId : public ReplacingCallbackASTVisitor {
  Cache *cache = nullptr;
  std::string from, to;
  Expr *transform(Expr *e) override {
    if (!e)
      return e;
    if (auto id = cast<IdExpr>(e)) {
      if (id->getValue() != from)
        return e;
      auto n = cache->N<IdExpr>(to);
      n->setSrcInfo(id->getSrcInfo());
      return n;
    }
    e->accept(*this);
    return e;
  }
  Stmt *transform(Stmt *s) override {
    if (s)
      s->accept(*this);
    return s;
  }
};

/// Calls fn on each slot of the scope that holds a statement, also inside compound statements, not inside defs,
/// classes or lambdas. `nested` is false for the statements of the scope's own suite.
void nesForEachScopeStmt(Stmt *s, bool nested, const std::function<void(Stmt *&, bool)> &fn) {
  auto suite = cast<SuiteStmt>(s);
  if (!suite)
    return;
  for (auto &x : *suite) {
    if (!x)
      continue;
    if (cast<SuiteStmt>(x)) {
      nesForEachScopeStmt(x, nested, fn);
      continue;
    }
    fn(x, nested);
    if (auto i = cast<IfStmt>(x)) {
      nesForEachScopeStmt(i->getIf(), true, fn);
      nesForEachScopeStmt(i->getElse(), true, fn);
    } else if (auto w = cast<WhileStmt>(x)) {
      nesForEachScopeStmt(w->getSuite(), true, fn);
      nesForEachScopeStmt(w->getElse(), true, fn);
    } else if (auto f = cast<ForStmt>(x)) {
      nesForEachScopeStmt(f->getSuite(), true, fn);
      nesForEachScopeStmt(f->getElse(), true, fn);
    } else if (auto t = cast<TryStmt>(x)) {
      nesForEachScopeStmt(t->getSuite(), true, fn);
      for (auto *c : *t)
        nesForEachScopeStmt(c->getSuite(), true, fn);
      nesForEachScopeStmt(t->getElse(), true, fn);
      nesForEachScopeStmt(t->getFinally(), true, fn);
    } else if (auto w = cast<WithStmt>(x)) {
      nesForEachScopeStmt(w->getSuite(), true, fn);
    }
  }
}
} // namespace

void ScopingVisitor::nesConditionalDefs(Stmt *body) {
  std::unordered_map<std::string, std::pair<int, bool>> defs; // name -> {count, one is nested}
  auto isOverload = [](FunctionStmt *f) {
    for (auto *d : f->getDecorators())
      if (isId(d, "overload"))
        return true;
    return false;
  };
  nesForEachScopeStmt(body, false, [&](Stmt *&x, bool nested) {
    if (auto f = cast<FunctionStmt>(x); f && !isOverload(f)) {
      auto &d = defs[f->getName()];
      d.first++;
      d.second = d.second || nested;
    }
  });
  std::unordered_map<std::string, int> counter;
  nesForEachScopeStmt(body, false, [&](Stmt *&x, bool) {
    auto f = cast<FunctionStmt>(x);
    if (!f || isOverload(f))
      return;
    auto name = f->getName();
    auto d = defs[name];
    if (d.first < 2 || !d.second)
      return;
    auto newName = fmt::format("_nes_def_{}_{}", name, ++counter[name]);
    NesRenameId r;
    r.cache = ctx->cache;
    r.from = name;
    r.to = newName;
    r.transform(f->getSuite());
    f->setName(newName);
    auto assign = N<AssignStmt>(N<IdExpr>(name), N<IdExpr>(newName));
    assign->setSrcInfo(f->getSrcInfo());
    x = N<SuiteStmt>(f, assign);
  });
}

void ScopingVisitor::visit(FunctionStmt *stmt) {
  TypecheckVisitor::nesForwardReferences(ctx->cache, stmt);
  nesConditionalDefs(stmt->getSuite());
  // Validate
  std::vector<Expr *> newDecorators;
  for (auto &d : stmt->getDecorators()) {
    if (isId(d, "__attribute__")) {
      stmt->setAttribute(Attr::Attribute);
    } else if (isId(d, "llvm")) {
      stmt->setAttribute(Attr::LLVM);
    } else if (isId(d, "python")) {
      if (stmt->getDecorators().size() != 1)
        STOP_ERROR(Error::FN_SINGLE_DECORATOR, stmt->getDecorators()[1], "python");
      stmt->setAttribute(Attr::Python);
    } else if (isId(d, "__internal__")) {
      stmt->setAttribute(Attr::Internal);
    } else if (isId(d, "__hidden__")) {
      stmt->setAttribute(Attr::HiddenFromUser);
    } else if (isId(d, "atomic")) {
      stmt->setAttribute(Attr::Atomic);
    } else if (isId(d, "property")) {
      stmt->setAttribute(Attr::Property);
    } else if (isId(d, "cached_property") ||
               (cast<DotExpr>(d) && cast<DotExpr>(d)->getMember() == "cached_property" &&
                isId(cast<DotExpr>(d)->getExpr(), "functools"))) {
      // NES: functools.cached_property is a property that is computed again at every access: compiled objects have no
      // __dict__ to keep the value. The result is the same for a method that only computes from the object's fields.
      stmt->setAttribute(Attr::Property);
    } else if (isId(d, "staticmethod")) {
      stmt->setAttribute(Attr::StaticMethod);
    } else if (isId(d, "classmethod")) {
      // NES: a classmethod is a static method whose first parameter (cls) is a type parameter; access passes the
      // class (`C.m(x)` -> `C.m(C, x)`, `obj.m(x)` -> `C.m(type(obj), x)`), so `cls(...)` and `cls.attr` resolve at
      // compile time, also for a subclass that inherits the method.
      stmt->setAttribute(Attr::StaticMethod);
      stmt->setAttribute(Attr::ClassMethod);
      for (auto &a : *stmt) {
        a.type = N<IdExpr>(TYPE_TYPE);
        break;
      }
    } else if (isId(d, "__force__")) {
      stmt->setAttribute(Attr::ForceRealize);
    } else if (isId(d, "C")) {
      stmt->setAttribute(Attr::C);
    } else {
      newDecorators.emplace_back(d);
    }
  }
  if (stmt->hasAttribute(Attr::C)) {
    for (auto &a : *stmt) {
      if (a.getName().size() > 1 && a.getName()[0] == '*' && a.getName()[1] != '*')
        stmt->setAttribute(Attr::CVarArg);
    }
  }
  if (!stmt->empty() && !stmt->front().getType() && stmt->front().getName() == "self") {
    stmt->setAttribute(Attr::HasSelf);
  }
  stmt->setDecorators(newDecorators);
  if (!stmt->getReturn() &&
      (stmt->hasAttribute(Attr::LLVM) || stmt->hasAttribute(Attr::C)))
    STOP_ERROR(Error::FN_LLVM, getSrcInfo());
  // Set attributes
  std::unordered_set<std::string> seenArgs;
  bool defaultsStarted = false, hasStarArg = false, hasKwArg = false;
  for (size_t ia = 0; ia < stmt->size(); ia++) {
    auto &a = (*stmt)[ia];
    auto [stars, n] = a.getNameWithStars();
    if (stars == 2) {
      if (hasKwArg)
        STOP_ERROR(Error::FN_MULTIPLE_ARGS, a.getSrcInfo());
      if (a.getDefault())
        STOP_ERROR(Error::FN_DEFAULT_STARARG, a.getDefault());
      if (ia != stmt->size() - 1)
        STOP_ERROR(Error::FN_LAST_KWARG, a.getSrcInfo());

      hasKwArg = true;
    } else if (stars == 1) {
      if (hasStarArg)
        STOP_ERROR(Error::FN_MULTIPLE_ARGS, a.getSrcInfo());
      if (a.getDefault())
        STOP_ERROR(Error::FN_DEFAULT_STARARG, a.getDefault());
      hasStarArg = true;
    }
    if (in(seenArgs, n))
      STOP_ERROR(Error::FN_ARG_TWICE, a.getSrcInfo(), n);
    seenArgs.insert(n);
    if (!a.getDefault() && defaultsStarted && !stars && a.isValue())
      STOP_ERROR(Error::FN_DEFAULT, a.getSrcInfo(), n);
    defaultsStarted |= static_cast<bool>(a.getDefault());
    if (stmt->hasAttribute(Attr::C)) {
      if (a.getDefault())
        STOP_ERROR(Error::FN_C_DEFAULT, a.getDefault(), n);
      if (stars != 1 && !a.getType())
        STOP_ERROR(Error::FN_C_TYPE, a.getSrcInfo(), n);
    }
  }

  bool isOverload = false;
  for (auto &d : stmt->getDecorators())
    if (isId(d, "overload")) {
      isOverload = true;
    }
  if (!isOverload)
    visitName(stmt->getName(), true, stmt, stmt->getSrcInfo());

  auto c = std::make_shared<ScopingVisitor::Context>();
  c->cache = ctx->cache;
  c->functionScope = stmt;
  if (ctx->inClass && !stmt->empty())
    c->classDeduce = {stmt->front().getName(), {}};
  c->renames = ctx->renames;
  c->functionCaptures = ctx->functionCaptures;
  ScopingVisitor v;
  c->scope.emplace_back(0);
  v.ctx = c;
  v.visitName(stmt->getName(), true, stmt, stmt->getSrcInfo());
  for (const auto &a : *stmt) {
    auto [_, n] = a.getNameWithStars();
    v.visitName(n, true, stmt, a.getSrcInfo());
    if (a.defaultValue)
      CHECK(transform(a.defaultValue));
  }
  c->scope.pop_back();

  c->scope.emplace_back(0, stmt->getSuite());
  v.transform(stmt->getSuite());
  v.processChildCaptures();
  c->scope.pop_back();
  if (v.hasErrors())
    errors.append(v.errors);
  if (!canContinue())
    return;

  // Reading a nested function of an enclosing function also captures what that function captures (unless bound here).
  for (bool changed = true; changed;) {
    changed = false;
    std::vector<std::string> read;
    for (const auto &[name, _] : c->captures)
      read.push_back(name);
    for (const auto &name : read) {
      if (auto nested = in(c->functionCaptures, name)) {
        for (const auto &[captured, type] : *nested) {
          if (!in(c->captures, captured) && !in(c->map, captured)) {
            c->captures[captured] = type;
            changed = true;
          }
        }
      }
    }
  }
  if (ctx->functionScope && !c->captures.empty())
    ctx->functionCaptures[stmt->getName()] = c->captures;

  auto b = std::make_unique<BindingsAttribute>();
  b->captures = c->captures;
  for (const auto &n : c->captures) {
    ctx->childCaptures.insert(n);
  }
  // Recursive capture if used
  if (c->map[stmt->getName()].size() == 1 && in(c->firstSeen, stmt->getName()))
    b->captures[stmt->getName()] = BindingsAttribute::Read;
  for (auto &[u, v] : c->map) {
    b->bindings[u] = {u, v.size()};
    auto cp = in(c->childCaptures, u);
    if (!cp)
      cp = in(c->captures, u);
    if (cp && *cp == BindingsAttribute::Nonlocal) {
      b->bindings[u].isNonlocal = true;
      ctx->childCaptures[u] = BindingsAttribute::Nonlocal;
    }
  }
  stmt->setAttribute(Attr::Bindings, std::move(b));

  if (!c->classDeduce.second.empty()) {
    auto s = std::make_unique<ir::StringListAttribute>();
    for (const auto &n : c->classDeduce.second)
      s->values.push_back(n);
    stmt->setAttribute(Attr::ClassDeduce, std::move(s));
  }
}

void ScopingVisitor::visit(WithStmt *stmt) {
  ConditionalBlock c(ctx.get(), stmt->getSuite());
  for (size_t i = 0; i < stmt->size(); i++) {
    CHECK(transform((*stmt)[i]));
    if (!stmt->getVars()[i].empty())
      visitName(stmt->getVars()[i], true, stmt, stmt->getSrcInfo());
  }
  CHECK(transform(stmt->getSuite()));
}

void ScopingVisitor::visit(ClassStmt *stmt) {
  // NES: `__class_getitem__ = classmethod(types.GenericAlias)` in a class body makes `C[int]` valid in type hints
  // (CPython's urllib.parse). Compiled code does not need it at run time, so the class variable is removed.
  TypecheckVisitor::nesDropClassGetItem(stmt);
  TypecheckVisitor::nesForwardReferences(ctx->cache, stmt);
  // @tuple(init=, repr=, eq=, order=, hash=, pickle=, container=, python=, add=,
  // internal=...)
  // @dataclass(...)
  // @extend

  std::map<std::string, bool> tupleMagics = {
      {"new", true},           {"repr", false},    {"hash", false},
      {"eq", false},           {"ne", false},      {"lt", false},
      {"le", false},           {"gt", false},      {"ge", false},
      {"pickle", true},        {"unpickle", true}, {"to_py", false},
      {"from_py", false},      {"iter", false},    {"getitem", false},
      {"len", false},          {"to_gpu", false},  {"from_gpu", false},
      {"from_gpu_new", false}, {"tuplesize", true}};

  // NES: `@functools.total_ordering` adds the comparison methods that the class does not define, from the first
  // defined one of __lt__, __le__, __gt__, __ge__ and __eq__, with the formulas of CPython's functools.
  {
    std::vector<Expr *> decorators;
    bool totalOrdering = false;
    for (auto *d : stmt->getDecorators()) {
      auto dot = cast<DotExpr>(d);
      if (isId(d, "total_ordering") ||
          (dot && dot->getMember() == "total_ordering" && isId(dot->getExpr(), "functools")))
        totalOrdering = true;
      else
        decorators.push_back(d);
    }
    if (totalOrdering) {
      stmt->setDecorators(decorators);
      std::unordered_set<std::string> defined;
      std::function<void(Stmt *)> collect = [&](Stmt *s) {
        if (auto f = cast<FunctionStmt>(s))
          defined.insert(f->getName());
        else if (auto suite = cast<SuiteStmt>(s))
          for (auto *x : *suite)
            collect(x);
      };
      collect(stmt->getSuite());
      // root -> {missing method, expression from r (the root's result), self and other}
      static const std::vector<std::pair<std::string, std::vector<std::pair<std::string, std::string>>>>
          conversions = {
              {"__lt__",
               {{"__gt__", "not r and self != other"}, {"__le__", "r or self == other"}, {"__ge__", "not r"}}},
              {"__le__",
               {{"__ge__", "not r or self == other"}, {"__lt__", "r and self != other"}, {"__gt__", "not r"}}},
              {"__gt__",
               {{"__lt__", "not r and self != other"}, {"__ge__", "r or self == other"}, {"__le__", "not r"}}},
              {"__ge__",
               {{"__le__", "not r or self == other"}, {"__gt__", "r and self != other"}, {"__lt__", "not r"}}}};
      std::string code;
      for (auto &[root, others] : conversions)
        if (defined.contains(root)) {
          for (auto &[name, expr] : others)
            if (!defined.contains(name))
              code += fmt::format("def {}(self, other) -> bool:\n    r = self.{}(other)\n    return {}\n", name,
                                  root, expr);
          break;
        }
      if (code.empty() && !defined.contains("__lt__") && !defined.contains("__le__") &&
          !defined.contains("__gt__") && !defined.contains("__ge__"))
        STOP_ERROR(Error::CUSTOM, stmt, "must define at least one ordering operation: < > <= >=");
      if (!code.empty()) {
        auto parsed = parseCode(ctx->cache, stmt->getSrcInfo().file, code, stmt->getSrcInfo().line);
        if (!parsed)
          STOP_ERROR(Error::CUSTOM, stmt, "total_ordering: could not generate the comparison methods");
        stmt->getSuite()->addStmt(*parsed);
      }
    }
  }
  // NES: `dataclasses.dataclass` is `dataclass`, and a dataclass has Python's defaults (repr=True, eq=True).
  auto isDataclass = [](Expr *e) {
    if (isId(e, "dataclass"))
      return true;
    auto dot = cast<DotExpr>(e);
    return dot && dot->getMember() == "dataclass" && isId(dot->getExpr(), "dataclasses");
  };
  for (auto &d : stmt->getDecorators()) {
    auto c = cast<CallExpr>(d);
    if (isDataclass(d) || (c && isDataclass(c->getExpr())))
      tupleMagics["repr"] = tupleMagics["eq"] = tupleMagics["ne"] = true;
  }
  for (auto &d : stmt->getDecorators()) {
    if (isId(d, "__notuple__")) {
      stmt->setAttribute(Attr::ClassNoTuple);
    } else if (isId(d, "__noextend__")) {
      stmt->setAttribute(Attr::NoExtend);
    } else if (isDataclass(d)) {
      stmt->setAttribute(Attr::Dataclass);
    } else if (auto c = cast<CallExpr>(d)) {
      if (isId(c->getExpr(), "tuple")) {
        stmt->setAttribute(Attr::Tuple);
        for (auto &val : tupleMagics | std::views::values)
          val = true;
      } else if (!isDataclass(c->getExpr())) {
        STOP_ERROR(Error::CLASS_BAD_DECORATOR, c->getExpr());
      } else if (stmt->hasAttribute(Attr::Tuple)) {
        STOP_ERROR(Error::CLASS_CONFLICT_DECORATOR, c, "dataclass", "tuple");
      }
      for (const auto &a : *c) {
        auto b = cast<BoolExpr>(a);
        if (!b)
          STOP_ERROR(Error::CLASS_NONSTATIC_DECORATOR, a.getSrcInfo());
        char val = static_cast<char>(b->getValue());
        if (a.getName() == "init") {
          tupleMagics["new"] = val;
        } else if (a.getName() == "repr") {
          tupleMagics["repr"] = val;
        } else if (a.getName() == "eq") {
          tupleMagics["eq"] = tupleMagics["ne"] = val;
        } else if (a.getName() == "order") {
          tupleMagics["lt"] = tupleMagics["le"] = tupleMagics["gt"] =
              tupleMagics["ge"] = val;
        } else if (a.getName() == "hash") {
          tupleMagics["hash"] = val;
        } else if (a.getName() == "pickle") {
          tupleMagics["pickle"] = tupleMagics["unpickle"] = val;
        } else if (a.getName() == "python") {
          tupleMagics["to_py"] = tupleMagics["from_py"] = val;
        } else if (a.getName() == "gpu") {
          tupleMagics["to_gpu"] = tupleMagics["from_gpu"] =
              tupleMagics["from_gpu_new"] = val;
        } else if (a.getName() == "container") {
          tupleMagics["iter"] = tupleMagics["getitem"] = val;
        } else if (a.getName() == "frozen" || a.getName() == "unsafe_hash") {
          // NES: Python's dataclass arguments. A frozen dataclass is hashable (its fields are not made read-only).
          tupleMagics["hash"] = tupleMagics["hash"] || val;
        } else if (a.getName() == "slots" || a.getName() == "match_args" ||
                   a.getName() == "weakref_slot") {
          // NES: no effect in Codon.
        } else {
          STOP_ERROR(Error::CLASS_BAD_DECORATOR_ARG, a.getSrcInfo());
        }
      }
    } else if (isId(d, "tuple")) {
      if (stmt->hasAttribute(Attr::Tuple))
        STOP_ERROR(Error::CLASS_MULTIPLE_DECORATORS, d, "tuple");
      stmt->setAttribute(Attr::Tuple);
      for (auto &val : tupleMagics | std::views::values) {
        val = true;
      }
    } else if (isId(d, "extend")) {
      stmt->setAttribute(Attr::Extend);
      if (stmt->getDecorators().size() != 1) {
        STOP_ERROR(
            Error::CLASS_SINGLE_DECORATOR,
            stmt->getDecorators()[stmt->getDecorators().front() == d]->getSrcInfo(),
            "extend");
      }
    } else if (isId(d, "__internal__")) {
      stmt->setAttribute(Attr::Internal);
    } else {
      STOP_ERROR(Error::CLASS_BAD_DECORATOR, d);
    }
  }
  // NES: untyped class variables (`PREFIX = "n="`) do not stop the inference of fields from __init__; annotated
  // items (fields, `ClassVar[...]`) still do.
  bool onlyClassVars = true;
  for (const auto &a : *stmt)
    if (a.getType())
      onlyClassVars = false;
  if (!stmt->hasAttribute(Attr::Tuple) && !stmt->hasAttribute(Attr::Internal) &&
      !stmt->hasAttribute(Attr::Dataclass) && stmt->getStaticBaseClasses().empty() &&
      onlyClassVars) {
    stmt->setAttribute(Attr::ClassDeduce);
  }
  if (!stmt->hasAttribute(Attr::Tuple)) {
    tupleMagics["init"] = tupleMagics["new"];
    tupleMagics["new"] = tupleMagics["raw"] = true;
    tupleMagics["len"] = false;
    tupleMagics["repr_default"] = true;
  }
  tupleMagics["dict"] = true;
  // Internal classes do not get any auto-generated members.
  std::vector<std::string> magics;
  if (!stmt->hasAttribute(Attr::Internal)) {
    for (auto &m : tupleMagics)
      if (m.second) {
        if (m.first == "new")
          magics.insert(magics.begin(), m.first);
        else
          magics.push_back(m.first);
      }
  }
  stmt->setAttribute(Attr::ClassMagic,
                     std::make_unique<ir::StringListAttribute>(magics));
  std::unordered_set<std::string> seen;
  if (stmt->hasAttribute(Attr::Extend) && !stmt->empty())
    STOP_ERROR(Error::CLASS_EXTENSION, stmt->front().getSrcInfo());
  if (stmt->hasAttribute(Attr::Extend) &&
      !(stmt->getBaseClasses().empty() && stmt->getStaticBaseClasses().empty())) {
    STOP_ERROR(Error::CLASS_EXTENSION, stmt->getBaseClasses().empty()
                                           ? stmt->getStaticBaseClasses().front()
                                           : stmt->getBaseClasses().front());
  }
  for (auto &a : *stmt) {
    if (!a.getType() && !a.getDefault())
      STOP_ERROR(Error::CLASS_MISSING_TYPE, a.getSrcInfo(), a.getName());
    if (in(seen, a.getName()))
      STOP_ERROR(Error::CLASS_ARG_TWICE, a.getSrcInfo(), a.getName());
    seen.insert(a.getName());
  }

  if (stmt->hasAttribute(Attr::Extend))
    visitName(stmt->getName());
  else
    visitName(stmt->getName(), true, stmt, stmt->getSrcInfo());

  auto c = std::make_shared<ScopingVisitor::Context>();
  c->cache = ctx->cache;
  c->renames = ctx->renames;
  ScopingVisitor v;
  c->scope.emplace_back(0);
  c->inClass = true;
  v.ctx = c;
  for (const auto &a : *stmt) {
    v.transform(a.type);
    v.transform(a.defaultValue);
  }
  v.transform(stmt->getSuite());
  c->scope.pop_back();
  if (v.hasErrors())
    errors.append(v.errors);
  if (!canContinue())
    return;

  for (auto &d : stmt->getBaseClasses())
    CHECK(transform(d));
  for (auto &d : stmt->getStaticBaseClasses())
    CHECK(transform(d));
}

void ScopingVisitor::processChildCaptures() {
  for (auto &n : ctx->childCaptures) {
    if (auto i = in(ctx->map, n.first)) {
      if (i->back().binding && cast<ClassStmt>(i->back().binding))
        continue;
    }
    if (!findDominatingBinding(n.first)) {
      ctx->captures.insert(n); // propagate!
    }
  }
}

void ScopingVisitor::switchToUpdate(ASTNode *binding, const std::string &name,
                                    bool gotUsedVar) {
  if (binding && binding->hasAttribute(Attr::Bindings)) {
    binding->getAttribute<BindingsAttribute>(Attr::Bindings)->bindings.erase(name);
  }
  if (binding) {
    if (!gotUsedVar && binding->hasAttribute(Attr::ExprDominatedUsed))
      binding->eraseAttribute(Attr::ExprDominatedUsed);
    binding->setAttribute(gotUsedVar ? Attr::ExprDominatedUsed : Attr::ExprDominated);
  }
  if (cast<FunctionStmt>(binding))
    STOP_ERROR(error::Error::ID_INVALID_BIND, binding, name);
  else if (cast<ClassStmt>(binding))
    STOP_ERROR(error::Error::ID_INVALID_BIND, binding, name);
}

bool ScopingVisitor::visitName(const std::string &name, bool adding, ASTNode *root,
                               const SrcInfo &src) {
  if (adding && ctx->inClass)
    return false;
  if (adding) {
    if (auto p = in(ctx->captures, name)) {
      if (*p == BindingsAttribute::CaptureType::Read) {
        addError(error::Error::ASSIGN_LOCAL_REFERENCE, ctx->firstSeen[name], name, src);
        return false;
      } else if (root) { // global, nonlocal
        switchToUpdate(root, name, false);
      }
    } else {
      if (auto i = in(ctx->childCaptures, name)) {
        if (*i != BindingsAttribute::CaptureType::Global && ctx->functionScope) {
          auto newScope = std::vector<int>{ctx->scope[0].id};
          seqassert(ctx->scope.front().suite, "invalid suite");
          if (!ctx->scope.front().suite->hasAttribute(Attr::Bindings))
            ctx->scope.front().suite->setAttribute(
                Attr::Bindings, std::make_unique<BindingsAttribute>());
          ctx->scope.front()
              .suite->getAttribute<BindingsAttribute>(Attr::Bindings)
              ->bindings[name] = {name, 0,
                                  *i == BindingsAttribute::CaptureType::Nonlocal};
          auto newItem = ScopingVisitor::Context::Item(src, newScope, nullptr);
          ctx->map[name].push_back(newItem);
        }
      }
      ctx->map[name].emplace_front(src, ctx->getScope(), root);
    }
  } else {
    if (!in(ctx->firstSeen, name))
      ctx->firstSeen[name] = src;
    if (!in(ctx->map, name)) {
      ctx->captures[name] = BindingsAttribute::CaptureType::Read;
    }
  }
  if (auto val = findDominatingBinding(name)) {
    // Track loop variables to dominate them later. Example:
    // x = 1
    // while True:
    //   if x > 10: break
    //   x = x + 1  # x must be dominated after the loop to ensure that it gets updated
    auto scope = ctx->getScope();
    for (size_t li = ctx->scope.size(); li-- > 0;) {
      if (ctx->scope[li].seenVars) {
        bool inside = val->scope.size() >= scope.size() &&
                      val->scope[scope.size() - 1] == scope.back();
        if (!inside)
          ctx->scope[li].seenVars->insert(name);
        else
          break;
      }
      scope.pop_back();
    }

    // Variable binding check for variables that are defined within conditional blocks
    if (!val->accessChecked.empty()) {
      bool checked = false;
      for (size_t ai = val->accessChecked.size(); ai-- > 0;) {
        auto &a = val->accessChecked[ai];
        if (a.size() <= ctx->scope.size() &&
            a[a.size() - 1] == ctx->scope[a.size() - 1].id) {
          checked = true;
          break;
        }
      }
      if (!checked) {
        seqassert(!adding, "bad branch");
        if (!(val->binding && val->binding->hasAttribute(Attr::Bindings))) {
          // If the expression is not conditional, we can just do the check once
          val->accessChecked.push_back(ctx->getScope());
        }
        return true;
      }
    }
  }
  return false;
}

/// Get an item from the context. Perform domination analysis for accessing items
/// defined in the conditional blocks (i.e., Python scoping).
ScopingVisitor::Context::Item *
ScopingVisitor::findDominatingBinding(const std::string &name, bool allowShadow) {
  auto it = in(ctx->map, name);
  if (!it || it->empty())
    return nullptr;
  auto lastGood = it->begin();
  while (lastGood != it->end() && lastGood->ignore)
    ++lastGood;
  int commonScope = static_cast<int>(ctx->scope.size());
  // Iterate through all bindings with the given name and find the closest binding that
  // dominates the current scope.
  for (auto i = it->begin(); i != it->end(); ++i) {
    if (i->ignore)
      continue;

    bool completeDomination = i->scope.size() <= ctx->scope.size() &&
                              i->scope.back() == ctx->scope[i->scope.size() - 1].id;
    if (completeDomination) {
      commonScope = i->scope.size();
      lastGood = i;
      break;
    } else {
      seqassert(i->scope[0] == 0, "bad scoping");
      seqassert(ctx->scope[0].id == 0, "bad scoping");
      // Find the longest block prefix between the binding and the current common scope.
      commonScope = std::min(commonScope, static_cast<int>(i->scope.size()));
      while (commonScope > 0 &&
             i->scope[commonScope - 1] != ctx->scope[commonScope - 1].id)
        commonScope--;
      // if (commonScope < int(ctx->scope.size()) && commonScope != p)
      //   break;
      lastGood = i;
    }
  }
  seqassert(lastGood != it->end(), "corrupted scoping ({})", name);
  if (!allowShadow) { // go to the end
    lastGood = it->end();
    --lastGood;
    int p = std::min(commonScope, static_cast<int>(lastGood->scope.size()));
    while (p >= 0 && lastGood->scope[p - 1] != ctx->scope[p - 1].id)
      p--;
    commonScope = p;
  }

  bool gotUsedVar = false;
  if (lastGood->scope.size() != commonScope) {
    // The current scope is potentially reachable by multiple bindings that are
    // not dominated by a common binding. Create such binding in the scope that
    // dominates (covers) all of them.
    auto scope = ctx->getScope();
    auto newScope = std::vector<int>(scope.begin(), scope.begin() + commonScope);

    // Make sure to prepend a binding declaration: `var` and `var__used__ = False`
    // to the dominating scope.
    for (size_t si = commonScope; si-- > 0; si--) {
      if (!ctx->scope[si].suite)
        continue;
      if (!ctx->scope[si].suite->hasAttribute(Attr::Bindings))
        ctx->scope[si].suite->setAttribute(Attr::Bindings,
                                           std::make_unique<BindingsAttribute>());
      ctx->scope[si]
          .suite->getAttribute<BindingsAttribute>(Attr::Bindings)
          ->bindings[name] = {name, 1};
      auto newItem = ScopingVisitor::Context::Item(
          getSrcInfo(), newScope, ctx->scope[si].suite, {lastGood->scope});
      lastGood = it->insert(++lastGood, newItem);
      gotUsedVar = true;
      break;
    }
  } else if (lastGood->binding && lastGood->binding->hasAttribute(Attr::Bindings)) {
    gotUsedVar = lastGood->binding->getAttribute<BindingsAttribute>(Attr::Bindings)
                     ->bindings[name]
                     .count > 0;
  }
  // Remove all bindings after the dominant binding.
  for (auto i = it->begin(); i != it->end(); ++i) {
    if (i == lastGood)
      break;
    switchToUpdate(i->binding, name, gotUsedVar);
    i->scope = lastGood->scope;
    i->ignore = true;
  }
  if (!gotUsedVar && lastGood->binding &&
      lastGood->binding->hasAttribute(Attr::Bindings))
    lastGood->binding->getAttribute<BindingsAttribute>(Attr::Bindings)
        ->bindings[name] = {name, 0};
  return &(*lastGood);
}

auto format_as(BindingsAttribute::CaptureType c) {
  return c == BindingsAttribute::Read ? "RD"
                                      : (c == BindingsAttribute::Global ? "GL" : "NL");
}

} // namespace codon::ast
