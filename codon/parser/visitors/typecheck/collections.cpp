// Copyright (C) 2022-2026 Exaloop Inc. <https://exaloop.io>

#include "codon/parser/ast.h"
#include "codon/parser/cache.h"
#include "codon/parser/common.h"
#include "codon/parser/peg/peg.h"
#include "codon/parser/visitors/scoping/scoping.h"
#include "codon/parser/visitors/typecheck/typecheck.h"

using namespace codon::error;

namespace codon::ast {

using namespace types;

/// Transform tuples.
/// @example
///   `(a1, ..., aN)` -> `Tuple.__new__(a1, ..., aN)`
void TypecheckVisitor::visit(TupleExpr *expr) {
  // In a table (a tuple of tuples of one length), an empty list in a column of lists gets the element type of the first
  // non-empty list there: `[]` becomes `List[type(e)]()`, with e its first element (type() does not evaluate e). Otherwise
  // the empty list is a List[NoneType], and code that loops over the table does not compile for that row. Only in user
  // code, as for the isinstance hooks.
  if (inUserCode() && expr->items.size() > 1) {
    auto rows = std::vector<TupleExpr *>();
    auto first = cast<TupleExpr>(expr->items[0]);
    for (auto *item : expr->items) {
      auto row = cast<TupleExpr>(item);
      if (first && row && row->items.size() == first->items.size())
        rows.push_back(row);
    }
    if (first && rows.size() == expr->items.size()) {
      for (size_t column = 0; column < rows[0]->items.size(); column++) {
        Expr *element = nullptr;
        bool allLists = true;
        for (auto *row : rows) {
          auto list = cast<ListExpr>(row->items[column]);
          if (!list) {
            allLists = false;
            break;
          }
          if (!element && !list->items.empty() && !cast<StarExpr>(list->items[0]))
            element = list->items[0];
        }
        if (!allLists || !element)
          continue;
        for (auto *row : rows)
          if (cast<ListExpr>(row->items[column])->items.empty())
            row->items[column] = N<CallExpr>(
                N<IndexExpr>(N<IdExpr>("List"), N<CallExpr>(N<IdExpr>("type"), clone(element))));
      }
    }
  }
  resultExpr =
      transform(N<CallExpr>(N<DotExpr>(N<IdExpr>(TYPE_TUPLE), "__new__"), expr->items));
}

/// Transform a list `[a1, ..., aN]` to the corresponding statement expression.
/// See @c transformComprehension
void TypecheckVisitor::visit(ListExpr *expr) {
  expr->setType(instantiateUnbound());
  auto name = getStdLibType("List")->name;
  if ((resultExpr = transformComprehension(name, "append", expr->items))) {
    resultExpr->setAttribute(Attr::ExprList);
  }
}

/// Transform a set `{a1, ..., aN}` to the corresponding statement expression.
/// See @c transformComprehension
void TypecheckVisitor::visit(SetExpr *expr) {
  expr->setType(instantiateUnbound());
  auto name = getStdLibType("Set")->name;
  if ((resultExpr = transformComprehension(name, "add", expr->items))) {
    resultExpr->setAttribute(Attr::ExprSet);
  }
}

/// Transform a dictionary `{k1: v1, ..., kN: vN}` to a corresponding statement
/// expression. See @c transformComprehension
namespace {
/// A Codon string literal with the bytes of value.
std::string nesStringLiteral(const std::string &value) {
  std::string out = "\"";
  for (unsigned char c : value) {
    if (c == '\\' || c == '"')
      out += fmt::format("\\{}", static_cast<char>(c));
    else if (c < 0x20 || c >= 0x7f)
      out += fmt::format("\\x{:02x}", c);
    else
      out += static_cast<char>(c);
  }
  return out + "\"";
}

/// The source of a record class for a dict literal with these keys: fields _f0... of the generic types T0..., and the
/// dict operations that a literal key selects at compile time.
std::string nesRecordSource(const std::string &name, const std::vector<std::string> &keys) {
  std::vector<std::string> generics, params, inits, keyLiterals, reprItems;
  std::string getitem, setitem, contains, get;
  for (size_t i = 0; i < keys.size(); i++) {
    auto k = nesStringLiteral(keys[i]);
    generics.push_back(fmt::format("T{}", i));
    params.push_back(fmt::format("f{0}: T{0}", i));
    inits.push_back(fmt::format("        self._f{0} = f{0}\n", i));
    keyLiterals.push_back(k);
    reprItems.push_back(fmt::format("repr({}) + \": \" + repr(self._f{})", k, i));
    getitem += fmt::format("        if key == {}:\n            return self._f{}\n", k, i);
    setitem += fmt::format("        if key == {}:\n            self._f{} = value\n            return\n", k, i);
    contains += fmt::format("        if key == {}:\n            return True\n", k);
    get += fmt::format("        if key == {}:\n            return self._f{}\n", k, i);
  }
  std::vector<std::string> fieldList, itemList;
  for (size_t i = 0; i < keys.size(); i++) {
    fieldList.push_back(fmt::format("self._f{}", i));
    itemList.push_back(fmt::format("({}, self._f{})", keyLiterals[i], i));
  }
  std::string src;
  src += fmt::format("class {}[{}]:\n", name, join(generics, ", "));
  for (size_t i = 0; i < keys.size(); i++)
    src += fmt::format("    _f{0}: T{0}\n", i);
  src += fmt::format("\n    def __init__(self, {}):\n{}", join(params, ", "), join(inits, ""));
  src += "\n    def __getitem__(self, key: Literal[str]):\n" + getitem + "        raise KeyError(repr(key))\n";
  src += "\n    def __setitem__(self, key: Literal[str], value):\n" + setitem +
         "        compile_error(\"a dict with values of different types cannot get a new key\")\n";
  src += "\n    def __contains__(self, key: Literal[str]) -> bool:\n" + contains + "        return False\n";
  src += fmt::format("\n    def __contains__(self, key: str) -> bool:\n        return key in ({},)\n",
                     join(keyLiterals, ", "));
  src += "\n    def get(self, key: Literal[str], default = None):\n" + get + "        return default\n";
  src += fmt::format("\n    def __len__(self) -> int:\n        return {}\n", keys.size());
  src += fmt::format("\n    def keys(self) -> List[str]:\n        return [{}]\n", join(keyLiterals, ", "));
  src += fmt::format("\n    def __iter__(self) -> Generator[str]:\n        yield from [{}]\n",
                     join(keyLiterals, ", "));
  // values() and items() are tuples: a loop over them is unrolled per value type.
  src += fmt::format("\n    def values(self):\n        return ({},)\n", join(fieldList, ", "));
  src += fmt::format("\n    def items(self):\n        return ({},)\n", join(itemList, ", "));
  src += fmt::format("\n    def __repr__(self) -> str:\n        return \"{{\" + \", \".join([{}]) + \"}}\"\n",
                     join(reprItems, ", "));
  src += "\n    def __str__(self) -> str:\n        return self.__repr__()\n";
  src += fmt::format("\n    def __as__(self, T: type):\n        return T({})\n", join(fieldList, ", "));
  src += fmt::format("\n    def _nes_record_keys(self) -> List[str]:\n        return [{}]\n",
                     join(keyLiterals, ", "));
  return src;
}
} // namespace

/// NES: a dict literal in a Python file whose keys are distinct string literals and whose values have types that do not
/// unify (`{"price": "$12", "sqft": 1200}`, the rows of the tuplex UDFs) is a record: a class with a field per key, whose
/// `row["sqft"]` (a literal key) has the type of that value. Codon's Dict has one value type, so such a literal did not
/// compile. A literal whose values unify stays a Dict.
Expr *TypecheckVisitor::transformNesRecord(DictExpr *expr, bool *delay) {
  if (!endswith(expr->getSrcInfo().file, ".py") || expr->items.size() < 2)
    return nullptr;
  std::vector<std::string> keys;
  for (auto *i : expr->items) {
    auto t = cast<TupleExpr>(i);
    if (!t || t->size() != 2)
      return nullptr;
    auto k = cast<StringExpr>((*t)[0]);
    if (!k || !k->isSimple() || std::ranges::find(keys, k->getValue()) != keys.end())
      return nullptr;
    keys.push_back(k->getValue());
  }
  std::vector<types::ClassType *> valueTypes;
  bool allKnown = true;
  for (auto *i : expr->items) {
    auto t = cast<TupleExpr>(i);
    (*t)[1] = transform((*t)[1]);
    // A value without a class is not typed yet; Codon's Dict path waits for it as well. A class with open generics
    // (e.g. List[T] of `[]`) is enough to decide, and the record's constructor infers the rest.
    auto vt = (*t)[1]->getClassType();
    // A literal has a static type (Literal[int] 1, Literal[int] 2, ...); its class is the non-static one.
    if (auto st = (*t)[1]->getType()->getStatic())
      vt = st->getNonStaticType()->getClass();
    if (!vt)
      allKnown = false;
    else
      valueTypes.push_back(vt);
  }
  if (!allKnown) {
    *delay = true;
    return nullptr;
  }
  auto compatible = [&](types::ClassType *a, types::ClassType *b) {
    // None fits every type; Optional[T] fits what T fits.
    if (a->is("NoneType") || b->is("NoneType"))
      return true;
    if (a->is(TYPE_OPTIONAL))
      a = extractClassGeneric(a)->getClass();
    if (b->is(TYPE_OPTIONAL))
      b = extractClassGeneric(b)->getClass();
    if (!a || !b || a->is("NoneType") || b->is("NoneType"))
      return true;
    if ((a->is("int") && b->is("float")) || (a->is("float") && b->is("int")))
      return true;
    types::Type::Unification us;
    auto score = a->unify(b, &us);
    us.undo();
    return score >= 0;
  };
  bool mixed = false;
  for (size_t i = 0; i < valueTypes.size() && !mixed; i++)
    for (size_t j = i + 1; j < valueTypes.size() && !mixed; j++)
      mixed = !compatible(valueTypes[i], valueTypes[j]);
  if (!mixed)
    return nullptr; // a Dict, as before

  // One class per key list: literals with the same keys (e.g. the returns of one function) have the same class, and a
  // record converts to another instance of it (__as__, e.g. str fields to Optional[str] fields).
  auto signature = join(keys, "\x1f");
  std::string canonical;
  if (auto c = in(ctx->cache->nesRecordClasses, signature)) {
    canonical = *c;
  } else {
    auto name = fmt::format("_NesRecord{}", ctx->cache->nesRecordClasses.size());
    auto code = nesRecordSource(name, keys);
    auto stmtOrErr = parseCode(ctx->cache, expr->getSrcInfo().file, code, expr->getSrcInfo().line);
    if (!stmtOrErr)
      throw exc::ParserException(stmtOrErr.takeError());
    auto cls = N<SuiteStmt>(*stmtOrErr);
    if (auto err = ast::ScopingVisitor::apply(ctx->cache, cls))
      throw exc::ParserException(std::move(err));
    prependStmts->push_back(transform(cls));
    auto val = ctx->find(name);
    seqassert(val && val->isType(), "record class {} not found", name);
    canonical = val->canonicalName;
    ctx->cache->nesRecordClasses[signature] = canonical;
  }
  std::vector<Expr *> args;
  for (auto *i : expr->items)
    args.push_back((*cast<TupleExpr>(i))[1]);
  return transform(N<CallExpr>(N<IdExpr>(canonical), args));
}

void TypecheckVisitor::visit(DictExpr *expr) {
  bool delay = false;
  if ((resultExpr = transformNesRecord(expr, &delay)))
    return;
  if (delay) {
    if (!expr->getType())
      expr->setType(instantiateUnbound());
    return;
  }
  expr->setType(instantiateUnbound());
  auto name = getStdLibType("Dict")->name;
  if ((resultExpr = transformComprehension(name, "__setitem__", expr->items))) {
    resultExpr->setAttribute(Attr::ExprDict);
  }
}

/// Transform a tuple generator expression.
/// @example
///   `tuple(expr for i in tuple_generator)` -> `Tuple.N.__new__(expr...)`
void TypecheckVisitor::visit(GeneratorExpr *expr) {
  // List comprehension optimization:
  // Use `iter.__len__()` when creating list if there is a single for loop
  // without any if conditions in the comprehension
  bool canOptimize =
      expr->kind == GeneratorExpr::ListGenerator && expr->loopCount() == 1;
  if (canOptimize) {
    auto iter = transform(clone(cast<ForStmt>(expr->getFinalSuite())->getIter()));
    auto ce = cast<CallExpr>(iter);
    if (IdExpr *id = nullptr; ce && ((id = cast<IdExpr>(ce->getExpr())))) {
      // Turn off this optimization for static items
      canOptimize &= !startswith(id->getValue(), "std.internal.static");
    }
  }

  Expr *var = N<IdExpr>(getTemporaryVar("gen"));
  if (expr->kind == GeneratorExpr::ListGenerator) {
    // List comprehensions
    expr->setFinalExpr(
        N<CallExpr>(N<DotExpr>(clone(var), "append"), expr->getFinalExpr()));
    auto suite = expr->getFinalSuite();
    auto noOptStmt =
        N<SuiteStmt>(N<AssignStmt>(clone(var), N<CallExpr>(N<IdExpr>("List"))), suite);

    if (canOptimize) {
      auto optimizeVar = getTemporaryVar("i");
      auto origIter = cast<ForStmt>(expr->getFinalSuite())->getIter();

      auto optStmt = clone(noOptStmt);
      cast<ForStmt>((*cast<SuiteStmt>(optStmt))[1])->iter = N<IdExpr>(optimizeVar);
      optStmt = N<SuiteStmt>(
          N<AssignStmt>(N<IdExpr>(optimizeVar), clone(origIter)),
          N<AssignStmt>(
              clone(var),
              N<CallExpr>(N<IdExpr>("List"),
                          N<CallExpr>(N<DotExpr>(N<IdExpr>(optimizeVar), "__len__")))),
          (*cast<SuiteStmt>(optStmt))[1]);
      resultExpr = N<IfExpr>(
          N<CallExpr>(N<IdExpr>("hasattr"), clone(origIter), N<StringExpr>("__len__")),
          N<StmtExpr>(optStmt, clone(var)), N<StmtExpr>(noOptStmt, var));
    } else {
      resultExpr = N<StmtExpr>(noOptStmt, var);
    }
    resultExpr = transform(resultExpr);
  } else if (expr->kind == GeneratorExpr::SetGenerator) {
    // Set comprehensions
    auto head = N<AssignStmt>(clone(var), N<CallExpr>(N<IdExpr>("Set")));
    expr->setFinalExpr(
        N<CallExpr>(N<DotExpr>(clone(var), "add"), expr->getFinalExpr()));
    auto suite = expr->getFinalSuite();
    resultExpr = transform(N<StmtExpr>(N<SuiteStmt>(head, suite), var));
  } else if (expr->kind == GeneratorExpr::DictGenerator) {
    // Dictionary comprehensions
    auto head = N<AssignStmt>(clone(var), N<CallExpr>(N<IdExpr>("Dict")));
    expr->setFinalExpr(N<CallExpr>(N<DotExpr>(clone(var), "__setitem__"),
                                   N<StarExpr>(expr->getFinalExpr())));
    auto suite = expr->getFinalSuite();
    resultExpr = transform(N<StmtExpr>(N<SuiteStmt>(head, suite), var));
  } else if (expr->kind == GeneratorExpr::TupleGenerator) {
    seqassert(expr->loopCount() == 1, "invalid tuple generator");
    auto gen = transform(cast<ForStmt>(expr->getFinalSuite())->getIter());
    if (!gen->getType()->canRealize())
      return; // Wait until the iterator can be realized

    auto block = N<SuiteStmt>();
    // `tuple = tuple_generator`
    auto tupleVar = getTemporaryVar("tuple");
    block->addStmt(N<AssignStmt>(N<IdExpr>(tupleVar), gen));

    auto forStmt = clone(cast<ForStmt>(expr->getFinalSuite()));
    auto finalExpr = expr->getFinalExpr();
    auto [ok, delay, preamble, staticItems] = transformStaticLoopCall(
        cast<ForStmt>(expr->getFinalSuite())->getVar(), &forStmt->suite, gen,
        [&](Stmt *wrap) { return N<StmtExpr>(clone(wrap), clone(finalExpr)); }, true);
    if (!ok)
      E(Error::CALL_BAD_ITER, gen, gen->getType()->prettyString());
    if (delay)
      return;

    std::vector<Expr *> tupleItems;
    for (auto &i : staticItems)
      tupleItems.push_back(cast<Expr>(i));
    if (preamble)
      block->addStmt(preamble);
    resultExpr = transform(N<StmtExpr>(block, N<TupleExpr>(tupleItems)));
  } else {
    expr->loops =
        transform(expr->getFinalSuite()); // assume: internal data will be changed
    if (!expr->getFinalExpr()) {
      // Case such as (0 for _ in static.range(2))
      // TODO: make this better.
      E(Error::CUSTOM, expr,
        "generator cannot be compiled. If using static tuple generator, use tuple(...) "
        "instead.");
    }
    unify(expr->getType(), instantiateType(getStdLibType("Generator"),
                                           {expr->getFinalExpr()->getType()}));
    if (realize(expr->getType()))
      expr->setDone();
  }
}

/// Transform a collection of type `type` to a statement expression:
///   `[a1, ..., aN]` -> `cont = [type](); (cont.[fn](a1); ...); cont`
/// Any star-expression within the collection will be expanded:
///   `[a, *b]` -> `cont.[fn](a); for i in b: cont.[fn](i)`.
/// @example
///   `[a, *b, c]`  -> ```cont = List(3)
///                       cont.append(a)
///                       for i in b: cont.append(i)
///                       cont.append(c)```
///   `{a, *b, c}`  -> ```cont = Set()
///                       cont.add(a)
///                       for i in b: cont.add(i)
///                       cont.add(c)```
///   `{a: 1, **d}` -> ```cont = Dict()
///                       cont.__setitem__((a, 1))
///                       for i in b.items(): cont.__setitem__((i[0], i[i]))```
Expr *TypecheckVisitor::transformComprehension(const std::string &type,
                                               const std::string &fn,
                                               std::vector<Expr *> &items) {
  // Deduce the super type of the collection--- in other words, the least common
  // ancestor of all types in the collection. For example, `type([1, 1.2]) == type([1.2,
  // 1]) == float` because float is an "ancestor" of int.
  // TODO: use wrapExpr...
  std::function<TypePtr(ClassType *, ClassType *)> superTyp = [&](ClassType *collectionCls,
                                                                  ClassType *ti) -> TypePtr {
    if (!collectionCls)
      return ti->shared_from_this();
    // NES: tuples of one size, element by element (`[("a", None), ("b", "x")]` is a list of Tuple[str, Optional[str]]).
    if (ti && collectionCls->is(TYPE_TUPLE) && ti->is(TYPE_TUPLE) && collectionCls->size() == ti->size() &&
        collectionCls->size() > 0 && collectionCls->name != ti->name) {
      // (differently named tuple classes are not merged)
    } else if (ti && collectionCls->is(TYPE_TUPLE) && ti->is(TYPE_TUPLE) && collectionCls->size() == ti->size() &&
               collectionCls->size() > 0 && endswith(getSrcInfo().file, ".py")) {
      std::vector<TypePtr> elements;
      bool changed = false;
      for (size_t i = 0; i < ti->size(); i++) {
        auto a = (*collectionCls)[i]->getClass();
        auto b = (*ti)[i]->getClass();
        TypePtr st = (a && b && a->realizedName() != b->realizedName()) ? superTyp(a, b) : nullptr;
        changed |= st != nullptr;
        elements.push_back(st ? st : (*collectionCls)[i]->shared_from_this());
      }
      if (changed)
        return instantiateType(generateTuple(elements.size()), ctx->cache->castVectorPtr(elements));
      return nullptr;
    }
    if (collectionCls->is("int") && ti->is("float")) {
      // Rule: int derives from float
      return ti->shared_from_this();
    } else if (collectionCls->name != TYPE_OPTIONAL && ti->name == TYPE_OPTIONAL) {
      // Rule: T derives from Optional[T]
      return instantiateType(getStdLibType("Optional"),
                             std::vector<types::Type *>{collectionCls});
    } else if (collectionCls->name == TYPE_OPTIONAL && ti->name != TYPE_OPTIONAL) {
      return instantiateType(getStdLibType("Optional"), std::vector<types::Type *>{ti});
    } else if (!collectionCls->is("pyobj") && ti->is("pyobj")) {
      // Rule: anything derives from pyobj
      return ti->shared_from_this();
    } else if (collectionCls->name != ti->name) {
      // Rule: subclass derives from superclass
      const auto &mros = getClass(collectionCls)->mro;
      for (size_t i = 1; i < mros.size(); i++) {
        auto t = instantiateType(mros[i].get(), collectionCls);
        if (t->unify(ti, nullptr) >= 0) {
          return ti->shared_from_this();
        }
      }
    }
    return nullptr;
  };

  TypePtr collectionTyp = instantiateUnbound();
  bool done = true;
  bool isDict = type == getStdLibType("Dict")->name;
  for (auto &i : items) {
    ClassType *typ = nullptr;
    if (!isDict && cast<StarExpr>(i)) {
      auto star = cast<StarExpr>(i);
      star->expr = transform(N<CallExpr>(N<DotExpr>(star->getExpr(), "__iter__")));
      if (star->getExpr()->getType()->is("Generator"))
        typ = extractClassGeneric(star->getExpr()->getType())->getClass();
    } else if (isDict && cast<KeywordStarExpr>(i)) {
      auto star = cast<KeywordStarExpr>(i);
      star->expr = transform(N<CallExpr>(N<DotExpr>(star->getExpr(), "items")));
      if (star->getExpr()->getType()->is("Generator"))
        typ = extractClassGeneric(star->getExpr()->getType())->getClass();
    } else {
      i = transform(i);
      typ = i->getClassType();
    }
    if (!typ) {
      done = false;
      continue;
    }
    if (!collectionTyp->getClass()) {
      unify(collectionTyp.get(), typ);
    } else if (!isDict) {
      if (auto t = superTyp(collectionTyp->getClass(), typ))
        collectionTyp = t;
    } else {
      auto tt = unify(typ, instantiateType(generateTuple(2)))->getClass();
      seqassert(collectionTyp->getClass() &&
                    collectionTyp->getClass()->generics.size() == 2 &&
                    tt->generics.size() == 2,
                "bad dict");
      std::vector<types::TypePtr> nt;
      for (int di = 0; di < 2; di++) {
        nt.push_back(extractClassGeneric(collectionTyp.get(), di)->shared_from_this());
        if (!nt[di]->getClass())
          unify(nt[di].get(), extractClassGeneric(tt, di));
        else if (auto dt = superTyp(nt[di]->getClass(),
                                    extractClassGeneric(tt, di)->getClass()))
          nt[di] = dt;
      }
      collectionTyp =
          instantiateType(generateTuple(nt.size()), ctx->cache->castVectorPtr(nt));
    }
  }
  if (!done)
    return nullptr;
  std::vector<Stmt *> stmts;
  Expr *var = N<IdExpr>(getTemporaryVar("cont"));

  std::vector<Expr *> constructorArgs{};
  if (type == getStdLibType("List")->name && !items.empty()) {
    // Optimization: pre-allocate the list with the exact number of elements
    constructorArgs.push_back(N<IntExpr>(items.size()));
  }
  auto t = N<IdExpr>(type);
  auto ta = instantiateType(getStdLibType(type));
  if (isDict && collectionTyp->getClass()) {
    seqassert(collectionTyp->getClass()->isRecord(), "bad dict");
    std::vector<types::Type *> nt;
    for (auto &g : collectionTyp->getClass()->generics)
      nt.push_back(g.getType());
    ta = instantiateType(getStdLibType(type), nt);
  } else if (!isDict) {
    ta = instantiateType(getStdLibType(type), {collectionTyp.get()});
  }
  t->setType(instantiateTypeVar(ta.get()));
  stmts.push_back(N<AssignStmt>(clone(var), N<CallExpr>(t, constructorArgs)));
  for (const auto &it : items) {
    if (!isDict && cast<StarExpr>(it)) {
      // Unpack star-expression by iterating over it
      // `*star` -> `for i in star: cont.[fn](i)`
      auto star = cast<StarExpr>(it);
      Expr *forVar = N<IdExpr>(getTemporaryVar("i"));
      star->getExpr()->setAttribute(Attr::ExprStarSequenceItem);
      stmts.push_back(N<ForStmt>(
          clone(forVar), star->getExpr(),
          N<ExprStmt>(N<CallExpr>(N<DotExpr>(clone(var), fn), clone(forVar)))));
    } else if (isDict && cast<KeywordStarExpr>(it)) {
      // Expand kwstar-expression by iterating over it: see the example above
      auto star = cast<KeywordStarExpr>(it);
      Expr *forVar = N<IdExpr>(getTemporaryVar("it"));
      star->getExpr()->setAttribute(Attr::ExprStarSequenceItem);
      stmts.push_back(N<ForStmt>(
          clone(forVar), star->getExpr(),
          N<ExprStmt>(N<CallExpr>(N<DotExpr>(clone(var), fn),
                                  N<IndexExpr>(clone(forVar), N<IntExpr>(0)),
                                  N<IndexExpr>(clone(forVar), N<IntExpr>(1))))));
    } else {
      it->setAttribute(Attr::ExprSequenceItem);
      if (isDict) {
        Expr *head = it, *lead = nullptr;
        if (hasSideEffect(head)) {
          auto var = getTemporaryVar("star");
          lead = N<AssignExpr>(N<IdExpr>(var), head);
          head = N<IdExpr>(var);
        } else {
          lead = clone(head);
        }
        lead->setAttribute(Attr::ExprSequenceItem);
        head->setAttribute(Attr::ExprSequenceItem);
        stmts.push_back(N<ExprStmt>(N<CallExpr>(N<DotExpr>(clone(var), fn),
                                                N<IndexExpr>(lead, N<IntExpr>(0)),
                                                N<IndexExpr>(head, N<IntExpr>(1)))));
      } else {
        it->setAttribute(Attr::ExprSequenceItem);
        stmts.push_back(N<ExprStmt>(N<CallExpr>(N<DotExpr>(clone(var), fn), it)));
      }
    }
  }
  return transform(N<StmtExpr>(stmts, var));
}

} // namespace codon::ast
