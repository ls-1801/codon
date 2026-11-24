// Copyright (C) 2022-2026 Exaloop Inc. <https://exaloop.io>

#include <string>
#include <tuple>

#include "codon/cir/attribute.h"
#include "codon/parser/ast.h"
#include "codon/parser/cache.h"
#include "codon/parser/common.h"
#include "codon/parser/match.h"
#include "codon/parser/visitors/scoping/scoping.h"
#include "codon/parser/visitors/typecheck/typecheck.h"

using namespace codon::error;
using namespace codon::matcher;

namespace codon::ast {

using namespace types;

/// Transform walrus (assignment) expression.
/// @example
///   `(expr := var)` -> `var = expr; var`
void TypecheckVisitor::visit(AssignExpr *expr) {
  auto a = N<AssignStmt>(clone(expr->getVar()), expr->getExpr());
  a->cloneAttributesFrom(expr);
  resultExpr = transform(N<StmtExpr>(a, expr->getVar()));
}

/// Transform assignments. Handle dominated assignments, forward declarations, static
/// assignments and type/function aliases.
/// See @c transformAssignment and @c unpackAssignments for more details.
/// See @c wrapExpr for more examples.
void TypecheckVisitor::visit(AssignStmt *stmt) {
  if (cast<TupleExpr>(stmt->lhs) || cast<ListExpr>(stmt->lhs)) {
    resultStmt = transform(unpackAssignment(stmt->lhs, stmt->rhs));
    return;
  }

  bool mustUpdate = stmt->isUpdate() || stmt->isAtomicUpdate();
  mustUpdate |= stmt->getLhs()->hasAttribute(Attr::ExprDominated);
  mustUpdate |= stmt->getLhs()->hasAttribute(Attr::ExprDominatedUsed);
  if (cast<BinaryExpr>(stmt->getRhs()) &&
      cast<BinaryExpr>(stmt->getRhs())->isInPlace()) {
    // Update case: a += b
    seqassert(!stmt->getTypeExpr(), "invalid AssignStmt {}", stmt->toString(0));
    mustUpdate = true;
  }

  resultStmt = transformAssignment(stmt, mustUpdate);
  if (stmt->getLhs()->hasAttribute(Attr::ExprDominatedUsed)) {
    // If this is dominated, set __used__ if needed
    stmt->getLhs()->eraseAttribute(Attr::ExprDominatedUsed);
    auto e = cast<IdExpr>(stmt->getLhs());
    seqassert(e, "dominated bad assignment");
    resultStmt = transform(N<SuiteStmt>(
        resultStmt,
        N<AssignStmt>(N<IdExpr>(fmt::format("{}{}", getUnmangledName(e->getValue()),
                                            VAR_USED_SUFFIX)),
                      N<BoolExpr>(true), nullptr, AssignStmt::UpdateMode::Update)));
  }
}

/// Transform deletions.
/// @example
///   `del a`    -> `a = type(a)()` and remove `a` from the context
///   `del a[x]` -> `a.__delitem__(x)`
void TypecheckVisitor::visit(DelStmt *stmt) {
  if (auto idx = cast<IndexExpr>(stmt->getExpr())) {
    resultStmt = N<ExprStmt>(transform(
        N<CallExpr>(N<DotExpr>(idx->getExpr(), "__delitem__"), idx->getIndex())));
  } else if (auto ei = cast<IdExpr>(stmt->getExpr())) {
    // Assign `a` to `type(a)()` to mark it for deletion
    resultStmt = transform(N<AssignStmt>(
        stmt->getExpr(),
        N<CallExpr>(N<CallExpr>(N<IdExpr>(TYPE_TYPE), clone(stmt->getExpr()))), nullptr,
        AssignStmt::Update));

    // Allow deletion *only* if the binding is dominated
    auto val = ctx->find(ei->getValue());
    if (!val)
      E(Error::ID_NOT_FOUND, ei, ei->getValue());
    if (ctx->getScope() != val->scope)
      E(Error::DEL_NOT_ALLOWED, ei, ei->getValue());
    ctx->remove(ei->getValue());
    ctx->remove(getUnmangledName(ei->getValue()));
  } else {
    E(Error::DEL_INVALID, stmt);
  }
}

/// Unpack an assignment expression `lhs = rhs` into a list of simple assignment
/// expressions (e.g., `a = b`, `a.x = b`, or `a[x] = b`).
/// Handle Python unpacking rules.
/// @example
///   `(a, b) = c`     -> `a = c[0]; b = c[1]`
///   `a, b = c`       -> `a = c[0]; b = c[1]`
///   `[a, *x, b] = c` -> `a = c[0]; x = c[1:-1]; b = c[-1]`.
/// Non-trivial right-hand expressions are first stored in a temporary variable.
/// @example
///   `a, b = c, d + foo()` -> `assign = (c, d + foo); a = assign[0]; b = assign[1]`.
/// Each assignment is unpacked recursively to allow cases like `a, (b, c) = d`.
Stmt *TypecheckVisitor::unpackAssignment(Expr *lhs, Expr *rhs) {
  std::vector<Expr *> leftSide;
  if (auto et = cast<TupleExpr>(lhs)) {
    // Case: (a, b) = ...
    for (auto *i : *et)
      leftSide.push_back(i);
  } else if (auto el = cast<ListExpr>(lhs)) {
    // Case: [a, b] = ...
    for (auto *i : *el)
      leftSide.push_back(i);
  } else {
    return N<AssignStmt>(lhs, rhs);
  }

  // Prepare the right-side expression
  auto oldSrcInfo = getSrcInfo();
  setSrcInfo(rhs->getSrcInfo());
  auto *block = N<SuiteStmt>();
  if (!cast<IdExpr>(rhs)) {
    // Store any non-trivial right-side expression into a variable. NES: other than a tuple or list display, through
    // __nes_unpack__, which makes a list of an iterable without __getitem__ (a generator, map(...)), as Python unpacks
    // any iterable. A display stays as it is: its None elements must keep their flexible type (`a, b = None, None`).
    auto var = getTemporaryVar("assign");
    auto newRhs = N<IdExpr>(var);
    Expr *value = ast::clone(rhs);
    if (!cast<TupleExpr>(rhs) && !cast<ListExpr>(rhs))
      value = N<CallExpr>(N<IdExpr>("__nes_unpack__"), value);
    block->addStmt(N<AssignStmt>(newRhs, value));
    rhs = newRhs;
  }

  // Process assignments until the fist StarExpr (if any)
  size_t st = 0;
  for (; st < leftSide.size(); st++) {
    if (cast<StarExpr>(leftSide[st]))
      break;
    // Transformation: `leftSide_st = rhs[st]` where `st` is static integer
    auto rightSide = N<IndexExpr>(ast::clone(rhs), N<IntExpr>(st));
    // Recursively process the assignment because of cases like `(a, (b, c)) = d)`
    auto ns = unpackAssignment(leftSide[st], rightSide);
    block->addStmt(ns);
  }
  // Process StarExpr (if any) and the assignments that follow it
  if (st < leftSide.size() && cast<StarExpr>(leftSide[st])) {
    // StarExpr becomes SliceExpr (e.g., `b` in `(a, *b, c) = d` becomes
    // `list(d[1:-2])`)
    Expr *rightSide = N<CallExpr>(
        N<IdExpr>(getMangledMethod("std.internal.types.array", "List", "as_list")),
        N<IndexExpr>(
            ast::clone(rhs),
            N<SliceExpr>(N<IntExpr>(st),
                         // this slice is either [st:] or [st:-lhs_len + st + 1]
                         leftSide.size() == st + 1
                             ? nullptr
                             : N<IntExpr>(-leftSide.size() + st + 1),
                         nullptr)));
    auto ns = unpackAssignment(cast<StarExpr>(leftSide[st])->getExpr(), rightSide);
    block->addStmt(ns);
    st += 1;
    // Process remaining assignments. They will use negative indices (-1, -2 etc.)
    // because we do not know how big is StarExpr
    for (; st < leftSide.size(); st++) {
      if (cast<StarExpr>(leftSide[st]))
        E(Error::ASSIGN_MULTI_STAR, leftSide[st]->getSrcInfo());
      rightSide = N<IndexExpr>(ast::clone(rhs),
                               N<IntExpr>(-static_cast<int>(leftSide.size() - st)));
      auto next = unpackAssignment(leftSide[st], rightSide);
      block->addStmt(next);
    }
  }
  setSrcInfo(oldSrcInfo);
  return block;
}

/// Transform simple assignments.
/// @example
///   `a[x] = b`    -> `a.__setitem__(x, b)`
///   `a.x = b`     -> @c AssignMemberStmt
///   `a: type` = b -> @c AssignStmt
///   `a = b`       -> @c AssignStmt or @c UpdateStmt (see below)
namespace {
/// NES: whether a method reads `self.<member>` or `cls.<member>`.
struct NesReadsAttr : public ReplacingCallbackASTVisitor {
  std::string self, member;
  bool found = false;
  Expr *transform(Expr *e) override {
    if (!e)
      return e;
    if (auto d = cast<DotExpr>(e))
      if (d->getMember() == member && (isId(d->getExpr(), self) || isId(d->getExpr(), "cls")))
        found = true;
    e->accept(*this);
    return e;
  }
  Stmt *transform(Stmt *s) override {
    if (s)
      s->accept(*this);
    return s;
  }
};
/// NES: the members that a method reads as `self.<member>` or `cls.<member>`.
/// NES: the members of `super().member` in a function.
/// Counts the bindings of a name: targets of assignments (also unpacking and in-place operators), for loops, `:=` and
/// `with ... as`. Nested functions count too, which only makes the count larger.
struct NesNameBindings : public ReplacingCallbackASTVisitor {
  std::string name;
  int count = 0;
  void countTarget(Expr *e) {
    if (!e)
      return;
    if (isId(e, name))
      count++;
    else if (auto t = cast<TupleExpr>(e))
      for (auto *i : *t)
        countTarget(i);
    else if (auto l = cast<ListExpr>(e))
      for (auto *i : *l)
        countTarget(i);
    else if (auto s = cast<StarExpr>(e))
      countTarget(s->getExpr());
  }
  Expr *transform(Expr *e) override {
    if (!e)
      return e;
    if (auto a = cast<AssignExpr>(e))
      countTarget(a->getVar());
    e->accept(*this);
    return e;
  }
  Stmt *transform(Stmt *s) override {
    if (!s)
      return s;
    if (auto a = cast<AssignStmt>(s))
      countTarget(a->getLhs());
    else if (auto f = cast<ForStmt>(s))
      countTarget(f->getVar());
    else if (auto w = cast<WithStmt>(s))
      for (auto &v : w->getVars())
        count += v == name;
    s->accept(*this);
    return s;
  }
};

struct NesSuperMembers : public ReplacingCallbackASTVisitor {
  std::set<std::string> members;
  Expr *transform(Expr *e) override {
    if (!e)
      return e;
    if (auto d = cast<DotExpr>(e))
      if (auto c = cast<CallExpr>(d->getExpr()); c && c->empty() && isId(c->getExpr(), "super"))
        members.insert(d->getMember());
    e->accept(*this);
    return e;
  }
  Stmt *transform(Stmt *s) override {
    if (s)
      s->accept(*this);
    return s;
  }
};

struct NesSelfMembers : public ReplacingCallbackASTVisitor {
  std::string self;
  std::set<std::string> members;
  Expr *transform(Expr *e) override {
    if (!e)
      return e;
    if (auto d = cast<DotExpr>(e))
      if (isId(d->getExpr(), self) || isId(d->getExpr(), "cls"))
        members.insert(d->getMember());
    // A builtin that calls a method of its argument (`str(self)` calls __str__) reads that method.
    static const std::map<std::string, std::string> builtins = {
        {"str", "__str__"},     {"repr", "__repr__"},   {"hash", "__hash__"}, {"int", "__int__"},
        {"float", "__float__"}, {"bool", "__bool__"},   {"len", "__len__"},   {"iter", "__iter__"},
        {"abs", "__abs__"},     {"format", "__format__"}};
    if (auto c = cast<CallExpr>(e))
      if (auto f = cast<IdExpr>(c->getExpr()))
        if (auto m = in(builtins, f->getValue()))
          for (auto &a : *c)
            if (isId(a.getExpr(), self))
              members.insert(*m);
    // An operator with self on the left (`self == other`, `self - 1`) reads its method.
    static const std::map<std::string, std::string> operators = {
        {"==", "__eq__"}, {"!=", "__ne__"},  {"<", "__lt__"},  {"<=", "__le__"}, {">", "__gt__"},
        {">=", "__ge__"}, {"+", "__add__"},  {"-", "__sub__"}, {"*", "__mul__"}, {"%", "__mod__"},
        {"&", "__and__"}, {"|", "__or__"},   {"^", "__xor__"}};
    if (auto b = cast<BinaryExpr>(e))
      if (isId(b->getLhs(), self))
        if (auto m = in(operators, b->getOp()))
          members.insert(*m);
    e->accept(*this);
    return e;
  }
  Stmt *transform(Stmt *s) override {
    if (s)
      s->accept(*this);
    return s;
  }
};
} // namespace

Stmt *TypecheckVisitor::transformAssignment(AssignStmt *stmt, bool mustExist) {
  if (auto idx = cast<IndexExpr>(stmt->getLhs())) {
    // Case: a[x] = b
    seqassert(!stmt->type, "unexpected type annotation");
    if (auto b = cast<BinaryExpr>(stmt->getRhs())) {
      // Case: a[x] += b (inplace operator)
      if (mustExist && b->isInPlace() && !cast<IdExpr>(b->getRhs())) {
        auto var = getTemporaryVar("assign");
        return transform(N<SuiteStmt>(
            N<AssignStmt>(N<IdExpr>(var), idx->getIndex()),
            N<ExprStmt>(N<CallExpr>(
                N<DotExpr>(idx->getExpr(), "__setitem__"), N<IdExpr>(var),
                N<BinaryExpr>(N<IndexExpr>(clone(idx->getExpr()), N<IdExpr>(var)),
                              b->getOp(), b->getRhs(), true)))));
      }
    }
    return transform(N<ExprStmt>(N<CallExpr>(N<DotExpr>(idx->getExpr(), "__setitem__"),
                                             idx->getIndex(), stmt->getRhs())));
  }

  if (auto dot = cast<DotExpr>(stmt->getLhs())) {
    // NES: `X.__doc__ = "..."` (also `X.field.__doc__`) only sets documentation, which compiled code does not keep: a
    // no-op, so that libraries such as CPython's urllib.parse compile.
    if (dot->getMember() == "__doc__")
      return transform(N<SuiteStmt>());
    // Case: a.x = b
    dot->expr = transform(dot->getExpr(), true);
    // NES: `C.attr = value` at module level, for an attribute that C does not declare (or only inherits): Python adds
    // a class attribute. It becomes a class variable of C (a global `<C>.attr`, as for one declared in the class
    // body), also for subclasses that inherit C's entry. The value may be a class (CPython's ipaddress:
    // `IPv4Network._constants = _IPv4Constants`); a subclass's own assignment overrides it.
    if (ctx->isGlobal() && isTypeExpr(dot->getExpr())) {
      auto ct = extractClassType(dot->getExpr());
      auto cls = ct ? getClass(ct) : nullptr;
      const auto &member = dot->getMember();
      if (cls && !findMember(ct, member) && findMethod(ct, member).empty()) {
        auto varName = fmt::format("{}.{}", ct->name, member);
        auto old = in(cls->classVars, member);
        std::string oldVar = old ? *old : "";
        std::vector<Stmt *> stmts;
        if (oldVar != varName) {
          stmts.push_back(transform(N<AssignStmt>(N<IdExpr>(varName), nullptr, nullptr)));
          auto val = ctx->forceFind(varName);
          val->baseName = "";
          val->scope = {0};
          registerGlobal(val->canonicalName);
          cls->classVars[member] = varName;
          for (auto &[name, sub] : ctx->cache->classes) {
            if (name == ct->name)
              continue;
            bool derived = false;
            for (auto &m : sub.mro)
              if (m && m->is(ct->name))
                derived = true;
            if (!derived)
              continue;
            auto subVar = in(sub.classVars, member);
            if (!subVar || *subVar == oldVar)
              sub.classVars[member] = varName;
          }
        }
        auto assign = N<AssignStmt>(N<IdExpr>(varName), stmt->getRhs());
        assign->setUpdate();
        stmts.push_back(transform(assign));
        if (!oldVar.empty() && oldVar != varName)
          if (auto copies = nesCopyInheritedReaders(ct, {member}))
            stmts.push_back(copies);
        return N<SuiteStmt>(stmts);
      }
    }
    return transform(N<AssignMemberStmt>(
        dot->getExpr(), dot->member, transform(stmt->getRhs()), stmt->getTypeExpr()));
  }

  // Case: a (: t) = b
  auto e = cast<IdExpr>(stmt->getLhs());
  if (!e) {
    E(Error::ASSIGN_INVALID, stmt->getLhs());
    return nullptr;
  }

  if (ctx->inFunction() && stmt->getRhs() && !mustExist) {
    if (auto b =
            ctx->getBase()->func->getAttribute<BindingsAttribute>(Attr::Bindings)) {
      const auto &bd = b->bindings[e->getValue()];
      if (bd.isNonlocal) {
        if (stmt->getTypeExpr())
          stmt->type = N<IndexExpr>(N<IdExpr>("Capsule"), stmt->getTypeExpr());
        else
          stmt->type = N<IdExpr>("Capsule");
      }
    }
  }

  bool isThreadLocal = false;
  auto typeExpr = transformType(stmt->getTypeExpr());
  if (typeExpr &&
      extractType(typeExpr)->is(getMangledClass("std.threading", "ThreadLocal"))) {
    isThreadLocal = true;
    if (auto ti = cast<IndexExpr>(stmt->getTypeExpr())) {
      typeExpr = transformType(ti->getIndex());
    } else {
      typeExpr = nullptr;
    }
  }

  // Make sure that existing values that cannot be shadowed are only updated
  // mustExist |= val && !ctx->isOuter(val);
  if (mustExist) {
    auto val = ctx->find(e->getValue(), getTime());
    if (!val)
      E(Error::ASSIGN_LOCAL_REFERENCE, e, e->getValue(), e->getSrcInfo());

    auto s = N<AssignStmt>(stmt->getLhs(), stmt->getRhs(), typeExpr);
    if (!ctx->getBase()->isType() && ctx->getBase()->func->hasAttribute(Attr::Atomic))
      s->setAtomicUpdate();
    else
      s->setUpdate();
    if (auto u = transformUpdate(s))
      return u;
    else
      return s; // delay
  }

  // NES: `x = isinstance(...)` (or hasattr) in a Python function, where x has no other binding: x is a static bool, as
  // `if isinstance(...)` is, so that `if x:` removes the branch that cannot run (CPython's urllib.parse:
  // `str_input = isinstance(args[0], str)`).
  bool nesStaticCandidate = false;
  if (!typeExpr && stmt->getRhs() && ctx->inFunction() && endswith(stmt->getSrcInfo().file, ".py"))
    if (auto c = cast<CallExpr>(stmt->getRhs()); c && (isId(c->getExpr(), "isinstance") || isId(c->getExpr(), "hasattr")))
      if (auto fn = getFunction(ctx->getBase()->name); fn && fn->origAst) {
        NesNameBindings nb;
        nb.name = e->getValue();
        nb.transform(fn->origAst->getSuite());
        nesStaticCandidate = nb.count == 1;
      }
  stmt->rhs = transform(stmt->getRhs(), true);
  if (nesStaticCandidate && stmt->getRhs()->getType()->getStaticKind() == LiteralKind::Bool)
    typeExpr = transformType(N<IndexExpr>(N<IdExpr>("Literal"), N<IdExpr>("bool")));
  stmt->type = typeExpr;

  // Generate new canonical variable name for this assignment and add it to the context
  auto canonical = ctx->generateCanonicalName(e->getValue());
  auto assign =
      N<AssignStmt>(N<IdExpr>(canonical), stmt->getRhs(), stmt->getTypeExpr());
  assign->getLhs()->cloneAttributesFrom(stmt->getLhs());
  assign->getLhs()->setType(stmt->getLhs()->getType()
                                ? stmt->getLhs()->getType()->shared_from_this()
                                : instantiateUnbound(assign->getLhs()->getSrcInfo()));
  if (isThreadLocal)
    assign->setThreadLocal();
  if (!stmt->getRhs() && !stmt->getTypeExpr() && ctx->find("NoneType")) {
    // All declarations that are not handled are to be marked with NoneType later on
    // (useful for dangling declarations that are not initialized afterwards due to
    //  static check)
    assign->getLhs()->getType()->getLink()->defaultType =
        getStdLibType("NoneType")->shared_from_this();
    ctx->getBase()->pendingDefaults[1].insert(
        assign->getLhs()->getType()->shared_from_this());
  }
  if (stmt->getTypeExpr()) {
    auto t = extractType(stmt->getTypeExpr());
    unify(assign->getLhs()->getType(),
          instantiateType(stmt->getTypeExpr()->getSrcInfo(), t));
  }
  auto val = std::make_shared<TypecheckItem>(
      canonical, ctx->getBaseName(), ctx->getModule(),
      assign->getLhs()->getType()->shared_from_this(), ctx->getScope());
  val->time = getTime();
  val->setSrcInfo(getSrcInfo());
  ctx->add(e->getValue(), val);
  ctx->addAlwaysVisible(val);

  if (assign->getRhs()) { // not a declaration!
    // Check if we can wrap the expression (e.g., `a: float = 3` -> `a = float(3)`)
    if (wrapExpr(&assign->rhs, assign->getLhs()->getType())) {
      unify(assign->getLhs()->getType(), assign->getRhs()->getType());
    }

    // Generalize non-variable types. That way we can support cases like:
    // `a = foo(x, ...); a(1); a('s')`
    if (!val->isVar()) {
      val->type = val->type->generalize(ctx->typecheckLevel - 1);
      // See capture_function_partial_proper_realize test
      assign->getLhs()->setType(val->type);
      assign->getRhs()->setType(val->type);
    }
  }

  // Mark declarations or generalized type/functions as done
  if ((!assign->getRhs() || assign->getRhs()->isDone()) &&
      assign->getLhs()->getType()->canRealize()) {
    if (auto r = realize(assign->getLhs()->getType())) {
      // overwrite types to remove dangling unbounds with some partials...
      assign->getLhs()->setType(r->shared_from_this());
      if (assign->getRhs())
        assign->getRhs()->setType(r->shared_from_this());
      assign->setDone();
    }
  } else if (assign->getRhs() && !val->isVar() && !val->type->hasUnbounds(false)) {
    assign->setDone();
  }

  // Register all toplevel variables as global in JIT mode
  //   OR if they are in imported module (not toplevel)
  bool isGlobal = (ctx->cache->isJit && val->isGlobal() && !val->isGeneric()) ||
                  (canonical == VAR_ARGV) ||
                  (val->isGlobal() && val->getModule() != "");
  if (isGlobal && val->isVar()) {
    registerGlobal(canonical);
    if (ctx->cache->isJit) {
      getImport(STDLIB_IMPORT)->ctx->addToplevel(getUnmangledName(val->getName()), val);
    }
  }

  return assign;
}

/// Transform binding updates. Special handling is done for atomic or in-place
/// statements (e.g., `a += b`).
/// See @c transformInplaceUpdate and @c wrapExpr for details.
Stmt *TypecheckVisitor::transformUpdate(AssignStmt *stmt) {
  stmt->lhs = transform(stmt->getLhs());

  // Check inplace updates
  auto [inPlace, inPlaceStmt] = transformInplaceUpdate(stmt);
  if (inPlace) {
    return inPlaceStmt;
  }

  // NES: a function defined on more than one path that runs (`if c: def f(): ... else: def f(): ...` with a
  // condition known only at run time; scoping made each def `_nes_def_f_N` plus `f = _nes_def_f_N`). Each def is its
  // own type, so the variable cannot hold both.
  if (auto lf = stmt->getLhs()->getType()->getFunc()) {
    auto rid = cast<IdExpr>(stmt->getRhs());
    if (rid && startswith(rid->getValue(), "_nes_def_") &&
        getUnmangledName(lf->ast->getName()) != rid->getValue())
      E(Error::CUSTOM, stmt,
        "function '{}' is defined differently on two paths that can run; Codon needs one definition (a static "
        "condition, such as isinstance(x, str), selects one at compile time)",
        rid->getValue().substr(9, rid->getValue().rfind('_') - 9));
  }

  stmt->rhs = transform(stmt->getRhs());
  stmt->type = transformType(stmt->getTypeExpr());
  if (stmt->getTypeExpr()) {
    unify(stmt->getLhs()->getType(), instantiateType(stmt->getTypeExpr()->getSrcInfo(),
                                                     extractType(stmt->getTypeExpr())));
  }

  // Case: wrap expressions if needed (e.g. floats or optionals)
  if (wrapExpr(&stmt->rhs, stmt->getLhs()->getType()))
    unify(stmt->getRhs()->getType(), stmt->getLhs()->getType());
  if (stmt->getRhs()->isDone() && realize(stmt->getLhs()->getType()))
    stmt->setDone();

  return nullptr;
}

/// Typecheck instance member assignments (e.g., `a.b = c`) and handle optional
/// instances. Disallow tuple updates.
/// @example
///   `opt.foo = bar` -> `unwrap(opt).foo = wrap(bar)`
/// See @c wrapExpr for more examples.
void TypecheckVisitor::visit(AssignMemberStmt *stmt) {
  stmt->lhs = transform(stmt->getLhs());

  if (auto lhsClass = extractClassType(stmt->getLhs())) {
    auto member = findMember(lhsClass, stmt->getMember());
    if (!member) {
      // Case: property setters
      auto setters = findMethod(
          lhsClass, fmt::format("{}{}", FN_SETTER_SUFFIX, stmt->getMember()));
      if (!setters.empty()) {
        resultStmt =
            transform(N<ExprStmt>(N<CallExpr>(N<IdExpr>(setters.front()->getFuncName()),
                                              stmt->getLhs(), stmt->getRhs())));
        return;
      }
      // Case: class variables
      if (auto cls = getClass(lhsClass))
        if (auto var = in(cls->classVars, stmt->getMember())) {
          auto a = N<AssignStmt>(N<IdExpr>(*var), transform(stmt->getRhs()));
          a->setUpdate();
          resultStmt = transform(a);
          return;
        }
    }
    if (!member && lhsClass->is(TYPE_OPTIONAL)) {
      // Unwrap optional and look up there
      resultStmt = transform(N<AssignMemberStmt>(
          N<CallExpr>(N<IdExpr>(FN_OPTIONAL_UNWRAP), stmt->getLhs()), stmt->getMember(),
          stmt->getRhs()));
      return;
    }
    // Case: __setattr__ support. Ensure that only Literal[str] arguments are accepted.
    if (!member) {
      auto u = instantiateUnbound(), v = instantiateUnbound();
      u->staticKind = LiteralKind::String;
      if (auto m =
              findBestMethod(lhsClass, "__setattr__", {lhsClass, u.get(), v.get()})) {
        if (m->funcGenerics.size() >= 1 &&
            extractFuncGeneric(m)->getStaticKind() == LiteralKind::String) {
          resultStmt = transform(N<ExprStmt>(
              N<CallExpr>(N<DotExpr>(stmt->getLhs(), "__setattr__"),
                          N<StringExpr>(stmt->getMember()), stmt->getRhs())));
          return;
        }
      }
    }

    if (!member) {
      E(Error::DOT_NO_ATTR, stmt->getLhs(), lhsClass->prettyString(),
        stmt->getMember());
      return;
    }
    if (lhsClass->isRecord()) // prevent tuple member assignment
      E(Error::ASSIGN_UNEXPECTED_FROZEN, stmt->getLhs());

    stmt->rhs = transform(stmt->getRhs());
    stmt->type = transformType(stmt->getTypeExpr());
    if (stmt->getTypeExpr()) {
      unify(stmt->getRhs()->getType(),
            instantiateType(stmt->getTypeExpr()->getSrcInfo(),
                            extractType(stmt->getTypeExpr())));
    }

    auto ftyp =
        instantiateType(stmt->getLhs()->getSrcInfo(), member->getType(), lhsClass);
    if (!ftyp->canRealize() && member->typeExpr) {
      unify(ftyp.get(), extractType(withClassGenerics(lhsClass, [&]() {
              return transform(clean_clone(member->typeExpr));
            })));
    }
    if (!wrapExpr(&stmt->rhs, ftyp.get()))
      return;
    unify(stmt->getRhs()->getType(), ftyp.get());

    if (stmt->getRhs()->isDone())
      stmt->setDone();
  }
}

/// Transform in-place and atomic updates.
/// @example
///   `a += b` -> `a.__iadd__(a, b)` if `__iadd__` exists
///   Capsule operations:
///   `a = b` -> a.val[0] = b
///   `a += b` -> a.val[0] += b
///   Atomic operations (when the needed magics are available):
///   `a = b`         -> `type(a).__atomic_xchg__(__ptr__(a), b)`
///   `a += b`        -> `type(a).__atomic_add__(__ptr__(a), b)`
///   `a = min(a, b)` -> `type(a).__atomic_min__(__ptr__(a), b)` (same for `max`)
/// @return a tuple indicating whether (1) the update statement can be replaced with an
///         expression, and (2) the replacement expression.
std::pair<bool, Stmt *> TypecheckVisitor::transformInplaceUpdate(AssignStmt *stmt) {
  // Case: capsule operations
  if (stmt->getLhs()->getType()->is("Capsule")) {
    return {true,
            transform(N<AssignStmt>(
                N<IndexExpr>(N<CallExpr>(N<IdExpr>(getMangledMethod("std.internal.core",
                                                                    "Capsule", "_ptr")),
                                         stmt->getLhs()),
                             N<IntExpr>(0)),
                stmt->getRhs()))};
  }

  // Case: in-place updates (e.g., `a += b`).
  // They are stored as `Update(a, Binary(a + b, inPlace=true))`
  auto bin = cast<BinaryExpr>(stmt->getRhs());
  if (bin && bin->isInPlace()) {
    bin->lexpr = transform(bin->getLhs());
    bin->rexpr = transform(bin->getRhs());

    if (!stmt->getRhs()->getType())
      stmt->getRhs()->setType(instantiateUnbound());
    if (bin->getLhs()->getClassType() && bin->getRhs()->getClassType()) {
      if (auto transformed = transformBinaryInplaceMagic(bin, stmt->isAtomicUpdate())) {
        unify(stmt->getRhs()->getType(), transformed->getType());
        return {true, transform(N<ExprStmt>(transformed))};
      } else if (!stmt->isAtomicUpdate()) {
        // If atomic, call normal magic and then use __atomic_xchg__ below
        return {false, nullptr};
      }
    } else { // Delay
      unify(stmt->getLhs()->getType(),
            unify(stmt->getRhs()->getType(), instantiateUnbound()));
      return {true, nullptr};
    }
  }

  // Case: atomic min/max operations.
  // Note: check only `a = min(a, b)`; does NOT check `a = min(b, a)`
  auto lhsClass = extractClassType(stmt->getLhs());
  auto call = cast<CallExpr>(stmt->getRhs());
  auto lei = cast<IdExpr>(stmt->getLhs());
  auto cei = call ? cast<IdExpr>(call->getExpr()) : nullptr;
  if (stmt->isAtomicUpdate() && call && lei && cei &&
      (cei->getValue() == "min" || cei->getValue() == "max") && call->size() == 2) {
    call->front().value = transform(call->front());
    if (cast<IdExpr>(call->front()) &&
        cast<IdExpr>(call->front())->getValue() == lei->getValue()) {
      // `type(a).__atomic_min__(__ptr__(a), b)`
      auto ptrTyp = instantiateType(stmt->getLhs()->getSrcInfo(), getStdLibType("Ptr"),
                                    std::vector<types::Type *>{lhsClass});
      (*call)[1].value = transform((*call)[1]);
      auto rhsTyp = extractClassType((*call)[1].value);
      if (auto method =
              findBestMethod(lhsClass, fmt::format("__atomic_{}__", cei->getValue()),
                             {ptrTyp.get(), rhsTyp})) {
        return {true,
                transform(N<ExprStmt>(N<CallExpr>(
                    N<IdExpr>(method->getFuncName()),
                    N<CallExpr>(N<IdExpr>("__ptr__"), stmt->getLhs()), (*call)[1])))};
      }
    }
  }

  // Case: atomic assignments
  if (stmt->isAtomicUpdate() && lhsClass) {
    // `type(a).__atomic_xchg__(__ptr__(a), b)`
    stmt->rhs = transform(stmt->getRhs());
    if (auto rhsClass = stmt->getRhs()->getClassType()) {
      auto ptrType = instantiateType(stmt->getLhs()->getSrcInfo(), getStdLibType("Ptr"),
                                     std::vector<types::Type *>{lhsClass});
      if (auto m =
              findBestMethod(lhsClass, "__atomic_xchg__", {ptrType.get(), rhsClass})) {
        return {true, transform(N<ExprStmt>(
                          N<CallExpr>(N<IdExpr>(m->getFuncName()),
                                      N<CallExpr>(N<IdExpr>("__ptr__"), stmt->getLhs()),
                                      stmt->getRhs())))};
      }
    }
  }

  return {false, nullptr};
}

/// NES: Codon compiles an inherited method once, for the base class, and resolves `self.attr` there. When class `ct`
/// has its own value of a class attribute that a base class also has (set in its body or from outside), the inherited
/// methods that read `self.attr` (or `cls.attr`) are copied into `ct`, as with @extend: they then see ct's value, and
/// calls through a base-class reference reach them by virtual dispatch. Returns the transformed extension, or nullptr.
Stmt *TypecheckVisitor::nesCopyInheritedReaders(types::ClassType *ct,
                                                const std::vector<std::string> &members) {
  auto cls = getClass(ct);
  if (!cls || members.empty())
    return nullptr;
  std::vector<Stmt *> copies;
  std::unordered_set<std::string> seen;
  for (auto &base : cls->mro) {
    if (!base || base->is(ct->name))
      continue;
    auto bcls = getClass(base.get());
    if (!bcls)
      continue;
    for (auto &[methodName, root] : bcls->methods) {
      if (in(cls->methods, methodName) || in(seen, methodName))
        continue;
      for (auto &overload : getOverloads(root)) {
        auto fn = getFunction(overload);
        auto f = fn ? fn->origAst : nullptr;
        if (!f || f->hasAttribute(Attr::AutoGenerated) || f->begin() == f->end())
          continue;
        bool reads = false;
        for (auto &member : members) {
          NesReadsAttr r;
          r.self = f->begin()->getName();
          r.member = member;
          r.transform(f->getSuite());
          reads |= r.found;
        }
        if (reads) {
          copies.push_back(clean_clone(f));
          seen.insert(methodName);
        }
      }
    }
  }
  if (copies.empty())
    return nullptr;
  auto ext = N<ClassStmt>(getUnmangledName(ct->name), std::vector<Param>{}, N<SuiteStmt>(copies),
                          std::vector<Expr *>{N<IdExpr>("extend")});
  auto wrapped = N<SuiteStmt>(ext);
  if (auto err = ScopingVisitor::apply(ctx->cache, wrapped))
    throw exc::ParserException(std::move(err));
  return transform(wrapped);
}

/// NES: a method of a base class that reads, through self, an attribute the base class does not have, but that a
/// subclass has (an abstract attribute: a class variable of a mixin such as `version = 4`, a method or a property of
/// the subclass). Codon compiles an inherited method once, for the base class, where the attribute is missing. Such a
/// method is copied into the subclass `ct` (as with @extend), and so is every inherited method that calls a copied one
/// through self, until no more are found. Returns the transformed extension, or nullptr.
Stmt *TypecheckVisitor::nesCopyAbstractReaders(types::ClassType *ct) {
  auto cls = getClass(ct);
  if (!cls || cls->mro.size() < 2)
    return nullptr;
  auto has = [&](types::ClassType *t, const std::string &m) {
    auto c = getClass(t);
    return findMember(t, m) || (c && in(c->classVars, m)) || !findMethod(t, m).empty();
  };
  struct Candidate {
    std::string name;
    types::ClassType *base;
    FunctionStmt *ast;
    std::set<std::string> reads;
  };
  std::vector<Candidate> candidates;
  std::unordered_set<std::string> names;
  for (auto &base : cls->mro) {
    if (!base || base->is(ct->name))
      continue;
    auto bcls = getClass(base.get());
    if (!bcls)
      continue;
    for (auto &[methodName, root] : bcls->methods) {
      if (in(cls->methods, methodName) || in(names, methodName))
        continue;
      // Only the method that the subclass resolves to (the first one in its MRO).
      auto resolved = findMethod(ct, methodName);
      if (resolved.empty() || getRootName(resolved.front()) != root)
        continue;
      for (auto &overload : getOverloads(root)) {
        auto fn = getFunction(overload);
        auto f = fn ? fn->origAst : nullptr;
        if (!f || f->hasAttribute(Attr::AutoGenerated) || f->begin() == f->end())
          continue;
        NesSelfMembers r;
        r.self = f->begin()->getName();
        r.transform(f->getSuite());
        candidates.push_back({methodName, base.get(), f, r.members});
      }
      names.insert(methodName);
    }
  }
  std::unordered_set<std::string> copied;
  for (bool changed = true; changed;) {
    changed = false;
    for (auto &c : candidates) {
      if (in(copied, c.name))
        continue;
      for (auto &m : c.reads)
        // An attribute the base class lacks, a copied method, or a method this class overrides (Python calls the
        // override through self; Codon compiles the inherited method once, for the base class).
        if (in(copied, m) || (has(ct, m) && !has(c.base, m)) || (in(cls->methods, m) && has(c.base, m))) {
          copied.insert(c.name);
          changed = true;
          break;
        }
    }
  }
  // `super().m` in a method of this class that resolves to a method of a base class that reads an abstract attribute
  // (`super().__str__()` in ipaddress.IPv6Address, where _BaseAddress.__str__ reads _string_from_ip_int): Python
  // runs that method with self of this class; Codon would run it for the base class. The method is copied into this
  // class as `_nes_super_<m>`, and `super().m` becomes `self._nes_super_<m>` (see visit(DotExpr)).
  std::vector<Stmt *> superCopies;
  {
    NesSuperMembers sm;
    for (auto &[methodName, root] : cls->methods)
      for (auto &overload : getOverloads(root))
        if (auto fn = getFunction(overload); fn && fn->origAst)
          sm.transform(fn->origAst->getSuite());
    for (auto &m : sm.members) {
      auto base = nesSuperBase(ct, m);
      if (!base)
        continue;
      auto bcls = getClass(base);
      auto root = bcls ? in(bcls->methods, m) : nullptr;
      if (!root)
        continue;
      for (auto &overload : getOverloads(*root)) {
        auto fn = getFunction(overload);
        auto f = fn ? fn->origAst : nullptr;
        if (!f || f->hasAttribute(Attr::AutoGenerated) || f->begin() == f->end())
          continue;
        NesSelfMembers r;
        r.self = f->begin()->getName();
        r.transform(f->getSuite());
        bool abstract = false;
        for (auto &read : r.members)
          if (in(copied, read) || (has(ct, read) && !has(base, read)))
            abstract = true;
        if (!abstract)
          continue;
        auto copy = clean_clone(f);
        copy->setName("_nes_super_" + m);
        superCopies.push_back(copy);
      }
    }
  }
  if (copied.empty() && superCopies.empty())
    return nullptr;
  std::vector<Stmt *> copies;
  for (auto &c : candidates)
    if (in(copied, c.name))
      copies.push_back(clean_clone(c.ast));
  for (auto *c : superCopies)
    copies.push_back(c);
  auto ext = N<ClassStmt>(getUnmangledName(ct->name), std::vector<Param>{}, N<SuiteStmt>(copies),
                          std::vector<Expr *>{N<IdExpr>("extend")});
  auto wrapped = N<SuiteStmt>(ext);
  if (auto err = ScopingVisitor::apply(ctx->cache, wrapped))
    throw exc::ParserException(std::move(err));
  return transform(wrapped);
}

/// NES: the class that `super().member` in a method of `ct` resolves to, as in Python: the first class after `ct` in
/// its MRO that defines the member (a method that is not generated, a field or a class variable). nullptr if none.
types::ClassType *TypecheckVisitor::nesSuperBase(types::ClassType *ct, const std::string &member) {
  auto cls = getClass(ct);
  if (!cls)
    return nullptr;
  for (auto &base : cls->mro) {
    if (!base || base->is(ct->name))
      continue;
    auto bcls = getClass(base.get());
    if (!bcls)
      continue;
    if (auto root = in(bcls->methods, member)) {
      for (auto &overload : getOverloads(*root))
        if (auto fn = getFunction(overload); fn && fn->ast && !fn->ast->hasAttribute(Attr::AutoGenerated))
          return base.get();
      continue;
    }
    if (in(bcls->classVars, member))
      return base.get();
    for (auto &f : bcls->fields)
      if (f.name == member)
        return base.get();
  }
  return nullptr;
}

} // namespace codon::ast
