// Copyright (C) 2022-2026 Exaloop Inc. <https://exaloop.io>

#include <memory>
#include <string>
#include <tuple>
#include <vector>

#include "codon/parser/ast.h"
#include "codon/parser/common.h"
#include "codon/parser/match.h"
#include "codon/parser/peg/peg.h"
#include "codon/parser/visitors/format/format.h"
#include "codon/parser/visitors/scoping/scoping.h"
#include "codon/parser/visitors/typecheck/typecheck.h"

using namespace codon::error;
using namespace codon::matcher;

namespace codon::ast {

/// Import and parse a new module into its own context.
/// Also handle special imports ( see @c transformSpecialImport ).
/// To simulate Python's dynamic import logic and import stuff only once,
/// each import statement is guarded as follows:
///   if not _import_N_done:
///     _import_N()
///     _import_N_done = True
/// See @c transformNewImport and below for more details.
void TypecheckVisitor::visit(ImportStmt *stmt) {
  seqassert(!ctx->inClass(), "imports within a class");
  if ((resultStmt = transformSpecialImport(stmt)))
    return;

  // Fetch the import
  auto components = getImportPath(stmt->getFrom(), stmt->getDots());
  auto path = combine2(components, "/");
  auto file = getImportFile(ctx->cache, path, ctx->getFilename(), false, stmt->getDots() > 0);
  if (!file) {
    if (stmt->getDots() == 0 && ctx->autoPython) {
      auto newStr = FormatVisitor::apply(stmt->getFrom());
      if (stmt->getWhat())
        newStr += "." + FormatVisitor::apply(stmt->getWhat());
      compilationWarning(fmt::format("importing '{}' from Python", newStr),
                         stmt->getSrcInfo().file, stmt->getSrcInfo().line,
                         stmt->getSrcInfo().col);
      auto exprOrErr = parseExpr(ctx->cache, newStr, stmt->getFrom()->getSrcInfo());
      if (!exprOrErr)
        throw exc::ParserException(exprOrErr.takeError());
      resultStmt = transform(N<ImportStmt>(N<IdExpr>("python"), exprOrErr->first,
                                           stmt->getArgs(), stmt->getReturnType(),
                                           stmt->getAs()));
      return;
    }

    std::string s(stmt->getDots(), '.');
    for (auto &c : components) {
      if (c == "..") {
        continue;
      } else if (!s.empty() && s.back() != '.') {
        s += "." + c;
      } else {
        s += c;
      }
    }
    bool allDot = true;
    for (auto cp : s)
      if (cp != '.') {
        allDot = false;
        break;
      }
    if (allDot && match(stmt->getWhat(), M<IdExpr>()))
      s = cast<IdExpr>(stmt->getWhat())->getValue();
    E(Error::IMPORT_NO_MODULE, stmt, s);
  }

  // If the file has not been seen before, load it into cache
  bool handled = true;
  if (!in(ctx->cache->imports, file->path)) {
    resultStmt = transformNewImport(*file);
    if (!resultStmt)
      handled = false; // we need an import
  }

  const auto &import = getImport(file->path);
  std::string importVar = import->importVar;
  if (!import->loadedAtToplevel)
    handled = false;

  // Construct `if _import_done.__invert__(): (_import(); _import_done = True)`.
  // Do not do this during the standard library loading (we assume that standard library
  // imports are "clean" and do not need guards). Note that the importVar is empty if
  // the import has been loaded during the standard library loading.
  if (!handled) {
    resultStmt = N<ExprStmt>(
        N<CallExpr>(N<IdExpr>(getMangledFunc("", fmt::format("{}_call", importVar)))));
    LOG_TYPECHECK("[import] loading {}", importVar);
  }

  // Import requested identifiers from the import's scope to the current scope
  if (!stmt->getWhat()) {
    // Case: import foo
    auto name = stmt->as.empty() ? path : stmt->getAs();
    auto e = ctx->forceFind(importVar);
    ctx->add(name, e);
  } else if (cast<IdExpr>(stmt->getWhat()) &&
             cast<IdExpr>(stmt->getWhat())->getValue() == "*") {
    // Case: from foo import *
    seqassert(stmt->getAs().empty(), "renamed star-import");
    // Just copy all symbols from import's context here.
    for (auto &[i, ival] : *(import->ctx)) {
      if ((!startswith(i, "_") || (ctx->isStdlibLoading && startswith(i, "__")))) {
        // Ignore all identifiers that start with `_` but not those that start with
        // `__` while the standard library is being loaded
        auto c = ival.front();
        if (c->isConditional() && i.find('.') == std::string::npos)
          c = import->ctx->find(i);
        // Imports should ignore noShadow property
        ctx->add(i, c);
      }
    }
  } else {
    // Case 3: from foo import bar
    auto i = cast<IdExpr>(stmt->getWhat());
    seqassert(i, "not a valid import what expression");
    auto c = import->ctx->find(i->getValue());
    // Make sure that we are importing an existing global symbol
    if (!c)
      E(Error::IMPORT_NO_NAME, i, i->getValue(), file->module);
    if (c->isConditional())
      c = import->ctx->find(i->getValue());
    // Imports should ignore noShadow property
    ctx->add(stmt->getAs().empty() ? i->getValue() : stmt->getAs(), c);
  }
  resultStmt = transform(!resultStmt ? N<SuiteStmt>() : resultStmt); // erase it
}

/// Transform special `from C` and `from python` imports.
/// See @c transformCImport, @c transformCDLLImport and @c transformPythonImport
Stmt *TypecheckVisitor::transformSpecialImport(const ImportStmt *stmt) {
  if (auto fi = cast<IdExpr>(stmt->getFrom())) {
    if (fi->getValue() == "C") {
      auto wi = cast<IdExpr>(stmt->getWhat());
      if (wi && !stmt->isCVar()) {
        // C function imports
        return transformCImport(wi->getValue(), stmt->getArgs(), stmt->getReturnType(),
                                stmt->getAs());
      } else if (wi) {
        // C variable imports
        return transformCVarImport(wi->getValue(), stmt->getReturnType(),
                                   stmt->getAs());
      } else if (auto de = cast<DotExpr>(stmt->getWhat())) {
        // dylib C imports
        return transformCDLLImport(de->getExpr(), de->getMember(), stmt->getArgs(),
                                   stmt->getReturnType(), stmt->getAs(),
                                   !stmt->isCVar());
      }
    } else if (fi->getValue() == "python" && stmt->getWhat()) {
      // Python imports
      return transformPythonImport(stmt->getWhat(), stmt->getArgs(),
                                   stmt->getReturnType(), stmt->getAs());
    }
  }
  return nullptr;
}

/// Transform Dot(Dot(a, b), c...) into "{a, b, c, ...}".
/// Useful for getting import paths.
std::vector<std::string> TypecheckVisitor::getImportPath(Expr *from,
                                                         size_t dots) const {
  std::vector<std::string> components; // Path components
  if (from) {
    for (; cast<DotExpr>(from); from = cast<DotExpr>(from)->getExpr())
      components.push_back(cast<DotExpr>(from)->getMember());
    seqassert(cast<IdExpr>(from), "invalid import statement");
    components.push_back(cast<IdExpr>(from)->getValue());
  }

  // Handle dots (i.e., `..` in `from ..m import x`)
  for (size_t i = 1; i < dots; i++)
    components.emplace_back("..");
  std::ranges::reverse(components);
  return components;
}

/// Transform a C function import.
/// @example
///   `from C import foo(int) -> float as f` ->
///   ```@.c
///      def foo(a1: int) -> float:
///        pass
///      f = foo # if altName is provided```
/// No return type implies void return type. *args is treated as C VAR_ARGS.
Stmt *TypecheckVisitor::transformCImport(const std::string &name,
                                         const std::vector<Param> &args, Expr *ret,
                                         const std::string &altName) {
  std::vector<Param> fnArgs;
  bool hasVarArgs = false;
  for (size_t ai = 0; ai < args.size(); ai++) {
    seqassert(args[ai].getName().empty(), "unexpected argument name");
    seqassert(!args[ai].getDefault(), "unexpected default argument");
    seqassert(args[ai].getType(), "missing type");
    if (cast<EllipsisExpr>(args[ai].getType()) && ai + 1 == args.size()) {
      // C VAR_ARGS support
      hasVarArgs = true;
      fnArgs.emplace_back("*args", nullptr, nullptr);
    } else {
      fnArgs.emplace_back(args[ai].getName().empty() ? fmt::format("a{}", ai)
                                                     : args[ai].getName(),
                          clone(args[ai].getType()), nullptr);
    }
  }
  auto _ = ctx->generateCanonicalName(name); // avoid canonicalName == name
  Stmt *f =
      N<FunctionStmt>(name, ret ? clone(ret) : N<IdExpr>("NoneType"), fnArgs, nullptr);
  f->setAttribute(Attr::C);
  if (hasVarArgs)
    f->setAttribute(Attr::CVarArg);
  f = transform(f); // Already in the preamble
  if (!altName.empty()) {
    auto v = ctx->find(altName);
    auto val = ctx->forceFind(name);
    ctx->add(altName, val);
    ctx->remove(name);
  }
  return f;
}

/// Transform a C variable import.
/// @example
///   `from C import foo: int as f` ->
///   ```f: int = "foo"```
Stmt *TypecheckVisitor::transformCVarImport(const std::string &name, Expr *type,
                                            const std::string &altName) {
  auto canonical = ctx->generateCanonicalName(name);
  auto typ = transformType(clone(type));
  auto val = ctx->addVar(
      altName.empty() ? name : altName, canonical,
      std::make_shared<types::LinkType>(extractClassType(typ)->shared_from_this()),
      getTime());
  auto s = N<AssignStmt>(N<IdExpr>(canonical), nullptr, typ);
  s->lhs->setAttribute(Attr::ExprExternVar);
  s->lhs->setType(val->type);
  s->lhs->setDone();
  s->setDone();
  return s;
}

/// Transform a dynamic C import.
/// @example
///   `from C import lib.foo(int) -> float as f` ->
///   `f = _dlsym(lib, "foo", Fn=Function[[int], float]); f`
/// No return type implies void return type.
Stmt *TypecheckVisitor::transformCDLLImport(Expr *dylib, const std::string &name,
                                            const std::vector<Param> &args, Expr *ret,
                                            const std::string &altName,
                                            bool isFunction) {
  Expr *type = nullptr;
  if (isFunction) {
    std::vector<Expr *> fnArgs{N<ListExpr>(), ret ? clone(ret) : N<IdExpr>("NoneType")};
    for (const auto &a : args) {
      seqassert(a.getName().empty(), "unexpected argument name");
      seqassert(!a.getDefault(), "unexpected default argument");
      seqassert(a.getType(), "missing type");
      cast<ListExpr>(fnArgs[0])->items.emplace_back(clone(a.getType()));
    }
    type = N<IndexExpr>(N<IdExpr>("Function"), N<TupleExpr>(fnArgs));
  } else {
    type = clone(ret);
  }

  Expr *c = clone(dylib);
  return transform(N<AssignStmt>(
      N<IdExpr>(altName.empty() ? name : altName),
      N<CallExpr>(N<IdExpr>("_dlsym"),
                  std::vector<CallArg>{CallArg(c), CallArg(N<StringExpr>(name)),
                                       CallArg{"Fn", type}})));
}

/// Transform a Python module and function imports.
/// @example
///   `from python import module as f` -> `f = pyobj._import("module")`
///   `from python import lib.foo(int) -> float as f` ->
///   ```def f(a0: int) -> float:
///        f = pyobj._import("lib")._getattr("foo")
///        return float.__from_py__(f(a0))```
/// If a return type is nullptr, the function just returns f (raw pyobj).
Stmt *TypecheckVisitor::transformPythonImport(Expr *what,
                                              const std::vector<Param> &args, Expr *ret,
                                              const std::string &altName) {
  // Get a module name (e.g., os.path)
  auto components = getImportPath(what);

  if (!ret && args.empty()) {
    // Simple import: `from python import foo.bar` -> `bar = pyobj._import("foo.bar")`
    return transform(
        N<AssignStmt>(N<IdExpr>(altName.empty() ? components.back() : altName),
                      N<CallExpr>(N<DotExpr>(N<IdExpr>("pyobj"), "_import"),
                                  N<StringExpr>(combine2(components, ".")))));
  }

  // Python function import:
  // `from python import foo.bar(int) -> float` ->
  // ```def bar(a1: int) -> float:
  //      f = pyobj._import("foo")._getattr("bar")
  //      return float.__from_py__(f(a1))```

  // f = pyobj._import("foo")._getattr("bar")
  auto call = N<AssignStmt>(
      N<IdExpr>("f"),
      N<CallExpr>(N<DotExpr>(N<CallExpr>(N<DotExpr>(N<IdExpr>("pyobj"), "_import"),
                                         N<StringExpr>(combine2(
                                             components, ".", 0,
                                             static_cast<int>(components.size()) - 1))),
                             "_getattr"),
                  N<StringExpr>(components.back())));
  // f(a1, ...)
  std::vector<Param> params;
  std::vector<Expr *> callArgs;
  for (int i = 0; i < args.size(); i++) {
    params.emplace_back(fmt::format("a{}", i), clone(args[i].getType()), nullptr);
    callArgs.emplace_back(N<IdExpr>(fmt::format("a{}", i)));
  }
  // `return ret.__from_py__(f(a1, ...))`
  auto retType = (ret && !cast<NoneExpr>(ret)) ? clone(ret) : N<IdExpr>("NoneType");
  auto retExpr = N<CallExpr>(N<DotExpr>(clone(retType), "__from_py__"),
                             N<DotExpr>(N<CallExpr>(N<IdExpr>("f"), callArgs), "p"));
  auto retStmt = N<ReturnStmt>(retExpr);
  // Create a function
  return transform(N<FunctionStmt>(altName.empty() ? components.back() : altName,
                                   retType, params, N<SuiteStmt>(call, retStmt)));
}

/// Import a new file into its own context and wrap its top-level statements into a
/// function to support Python-like runtime import loading.
/// @example
///   ```_import_[I]_done = False
///      def _import_[I]():
///        global [imported global variables]...
///        __name__ = [I]
///        [imported top-level statements]```
Stmt *TypecheckVisitor::transformNewImport(const ImportFile &file) {
  // Use a clean context to parse a new file
  auto moduleID = file.module;
  std::ranges::replace(moduleID, '.', '_');
  auto ictx = std::make_shared<TypeContext>(ctx->cache, file.path);
  ictx->isStdlibLoading = ctx->isStdlibLoading;
  ictx->moduleName = file;
  auto &import = ctx->cache->imports[file.path];
  import.update(file.module, file.path, ictx);
  import.loadedAtToplevel =
      getImport(ctx->moduleName.path)->loadedAtToplevel &&
      (ctx->isStdlibLoading || (ctx->isGlobal() && ctx->scope.size() == 1));
  auto importVar = import.importVar =
      getTemporaryVar(fmt::format("import_{}", moduleID));
  LOG_REALIZE("[import] initializing {} (location: {}, toplevel: {})", importVar,
              file.path, import.loadedAtToplevel);

  // __name__ = [import name]
  Stmt *n = nullptr;
  if (file.module != "internal.core") {
    // str is not defined when loading internal.core; __name__ is not needed anyway
    n = N<SuiteStmt>(
        N<AssignStmt>(N<IdExpr>("__name__"), N<StringExpr>(ictx->moduleName.module)),
        N<AssignStmt>(N<IdExpr>("__file__"), N<StringExpr>(ictx->moduleName.path)));
    ctx->addBlock();
    preamble->addStmt(transform(
        N<AssignStmt>(N<IdExpr>(importVar),
                      N<CallExpr>(N<IdExpr>("Import.__new__"), N<BoolExpr>(false),
                                  N<StringExpr>(file.path), N<StringExpr>(file.module)),
                      N<IdExpr>("Import"))));
    auto val = ctx->forceFind(importVar);
    ctx->popBlock();
    val->scope = {0};
    val->baseName = "";
    val->moduleName = MODULE_MAIN;
    val->time = 0;
    getImport(STDLIB_IMPORT)->ctx->addToplevel(importVar, val);
    registerGlobal(val->getName());
  }
  auto nodeOrErr = parseFile(ctx->cache, file.path);
  if (!nodeOrErr)
    throw exc::ParserException(nodeOrErr.takeError());
  if (auto overlay = ctx->cache->fs->overlay_for(file.path); !overlay.empty()) {
    auto overlayOrErr = parseFile(ctx->cache, overlay.string());
    if (!overlayOrErr)
      throw exc::ParserException(overlayOrErr.takeError());
    nesMergeOverlay(*nodeOrErr, *overlayOrErr, overlay.string());
  }
  auto tv = TypecheckVisitor(ictx, preamble);
  n = N<SuiteStmt>(n, tv.nesHoistFunctionImports(*nodeOrErr, file.path), *nodeOrErr);
  if (auto err = ScopingVisitor::apply(ctx->cache, n, &ictx->globalShadows))
    throw exc::ParserException(std::move(err));

  if (!ctx->cache->errors.empty())
    throw exc::ParserException(ctx->cache->errors);
  // Add comment to the top of import for easier dump inspection
  auto comment =
      N<CommentStmt>(fmt::format("import: {} at {}", file.module, file.path));
  auto suite = N<SuiteStmt>(comment, n);

  if (ctx->isStdlibLoading) {
    // When loading the standard library, imports are not wrapped.
    // We assume that the standard library has no recursive imports and that all
    // statements are executed before the user-provided code.
    return tv.transform(suite);
  } else {
    // Generate import identifier
    auto stmts = N<SuiteStmt>();
    auto ret = N<ReturnStmt>();
    ret->setAttribute(Attr::Internal); // do not trigger toplevel ReturnStmt error
    stmts->addStmt(N<IfStmt>(N<DotExpr>(N<IdExpr>(importVar), "loaded"), ret));
    stmts->addStmt(N<ExprStmt>(
        N<CallExpr>(N<IdExpr>("Import._set_loaded"),
                    N<CallExpr>(N<IdExpr>("__ptr__"), N<IdExpr>(importVar)))));
    stmts->addStmt(suite);

    // Wrap all imported top-level statements into a function.
    auto fnName = fmt::format("{}_call", importVar);
    Stmt *fn =
        N<FunctionStmt>(fnName, N<IdExpr>("NoneType"), std::vector<Param>{}, stmts);
    fn = tv.transform(fn);
    tv.realize(ictx->forceFind(fnName)->getType());
    preamble->addStmt(fn);
    // LOG_USER("[import] done importing {}", file.module);
  }
  return nullptr;
}

/// NES: a function-local import (`def f(): import random`) runs the module's top-level code at the first call of the
/// function. NES runs UDF calls with a per-invocation arena that it reuses, so the module's globals would point into
/// memory that later calls overwrite. In a .py module, every function-local import whose module resolves is also done
/// at the start of the module, unconditionally, under a hidden name: the module initializer then initializes the
/// imported module, and the function-local import finds it loaded (Codon emits no call, or a call that returns at the
/// `loaded` flag). Hoisted statements are recorded in cache->nesHoistedImports as "file:line"; a statement whose module
/// does not resolve is not hoisted, and compiling it fails as before. `from C` and `from python` imports are skipped.
Stmt *TypecheckVisitor::nesHoistFunctionImports(Stmt *module, const std::string &path) {
  if (!module || !endswith(path, ".py"))
    return nullptr;
  std::vector<ImportStmt *> found;
  std::function<void(Stmt *, int)> walk = [&](Stmt *s, int depth) {
    if (!s)
      return;
    if (auto suite = cast<SuiteStmt>(s)) {
      for (auto *x : *suite)
        walk(x, depth);
    } else if (auto f = cast<FunctionStmt>(s)) {
      walk(f->getSuite(), depth + 1);
    } else if (auto c = cast<ClassStmt>(s)) {
      walk(c->getSuite(), depth);
    } else if (auto im = cast<ImportStmt>(s)) {
      if (depth > 0)
        found.push_back(im);
    } else if (auto i = cast<IfStmt>(s)) {
      walk(i->getIf(), depth);
      walk(i->getElse(), depth);
    } else if (auto w = cast<WhileStmt>(s)) {
      walk(w->getSuite(), depth);
      walk(w->getElse(), depth);
    } else if (auto fo = cast<ForStmt>(s)) {
      walk(fo->getSuite(), depth);
      walk(fo->getElse(), depth);
    } else if (auto t = cast<TryStmt>(s)) {
      walk(t->getSuite(), depth);
      for (auto *e : *t)
        walk(e->getSuite(), depth);
      walk(t->getElse(), depth);
      walk(t->getFinally(), depth);
    } else if (auto wi = cast<WithStmt>(s)) {
      walk(wi->getSuite(), depth);
    }
  };
  walk(module, 0);
  if (found.empty())
    return nullptr;

  auto root = [](Expr *e) -> std::string {
    while (auto d = cast<DotExpr>(e))
      e = d->getExpr();
    if (auto id = cast<IdExpr>(e))
      return id->getValue();
    return "";
  };
  auto resolves = [&](Expr *from, size_t dots) {
    auto components = getImportPath(from, dots);
    return getImportFile(ctx->cache, combine2(components, "/"), path, false, dots > 0) != nullptr;
  };
  auto hoisted = N<SuiteStmt>();
  std::unordered_map<std::string, bool> lines;
  for (auto *im : found) {
    auto key = fmt::format("{}:{}", im->getSrcInfo().file, im->getSrcInfo().line);
    auto r = im->getFrom() ? root(im->getFrom()) : "";
    if (r == "C" || r == "python" || (im->getFrom() && cast<CallExpr>(im->getFrom()))) {
      lines[key] = false;
      continue;
    }
    bool ok = im->getFrom() && resolves(im->getFrom(), im->getDots());
    if (ok) {
      hoisted->addStmt(N<ImportStmt>(clone(im->getFrom()), nullptr, std::vector<Param>{}, nullptr,
                                     fmt::format("__nes_hoisted_import_{}", ctx->cache->nesHoistedImports.size() +
                                                                                 hoisted->size()),
                                     im->getDots()));
      // `from m import n` where n is a submodule: initialize n too
      if (auto what = cast<IdExpr>(im->getWhat()); what && what->getValue() != "*") {
        auto sub = N<DotExpr>(clone(im->getFrom()), what->getValue());
        if (resolves(sub, im->getDots()))
          hoisted->addStmt(N<ImportStmt>(sub, nullptr, std::vector<Param>{}, nullptr,
                                         fmt::format("__nes_hoisted_import_{}",
                                                     ctx->cache->nesHoistedImports.size() + hoisted->size()),
                                         im->getDots()));
      }
    }
    auto it = lines.find(key);
    lines[key] = ok && (it == lines.end() || it->second);
  }
  for (auto &[key, ok] : lines)
    if (ok)
      ctx->cache->nesHoistedImports.insert(key);
  for (auto *s : *hoisted)
    s->setSrcInfo(module->getSrcInfo());
  return hoisted->size() ? hoisted : nullptr;
}

/// NES: merge an overlay into a library module (a last resort for code that does not fit Codon's types, or that is
/// native in CPython). Top-level statements are matched by the name they bind (def, class, assignment to a name,
/// import):
/// - an overlay statement replaces the module's first statement of the same name, in its place, so the order of
///   module initialization stays;
/// - `__nes_remove__ = ["a", "b"]` removes the module's statements that bind these names;
/// - a class decorated with `@__nes_patch__` replaces or adds single members (methods, class variables) of the
///   module's class of that name;
/// - other overlay statements are appended.
void TypecheckVisitor::nesMergeOverlay(Stmt *module, Stmt *overlay, const std::string &overlayPath) {
  auto bound = [](Stmt *s) -> std::string {
    if (auto f = cast<FunctionStmt>(s))
      return f->getName();
    if (auto c = cast<ClassStmt>(s))
      return c->getName();
    if (auto a = cast<AssignStmt>(s))
      if (auto id = cast<IdExpr>(a->getLhs()))
        return id->getValue();
    if (auto im = cast<ImportStmt>(s)) {
      if (!im->getAs().empty())
        return im->getAs();
      if (auto w = cast<IdExpr>(im->getWhat()))
        return w->getValue() == "*" ? "" : w->getValue();
      if (!im->getWhat()) {
        Expr *e = im->getFrom();
        while (auto d = cast<DotExpr>(e))
          e = d->getExpr();
        if (auto id = cast<IdExpr>(e))
          return id->getValue();
      }
    }
    return "";
  };
  std::function<void(Stmt *, const std::function<void(Stmt *&)> &)> each =
      [&](Stmt *s, const std::function<void(Stmt *&)> &fn) {
        if (auto suite = cast<SuiteStmt>(s))
          for (auto &x : *suite) {
            if (cast<SuiteStmt>(x))
              each(x, fn);
            else if (x)
              fn(x);
          }
      };

  std::unordered_set<std::string> remove;
  std::vector<std::pair<std::string, Stmt *>> defs;
  std::unordered_set<std::string> patches;
  each(overlay, [&](Stmt *&x) {
    auto name = bound(x);
    if (name == "__nes_remove__") {
      if (auto l = cast<ListExpr>(cast<AssignStmt>(x)->getRhs()))
        for (auto *e : *l)
          if (auto str = cast<StringExpr>(e))
            remove.insert(str->getValue());
      return;
    }
    if (auto c = cast<ClassStmt>(x)) {
      std::vector<Expr *> decorators;
      bool patch = false;
      for (auto *d : c->getDecorators())
        if (isId(d, "__nes_patch__"))
          patch = true;
        else
          decorators.push_back(d);
      if (patch) {
        c->setDecorators(decorators);
        patches.insert(name);
      }
    }
    defs.emplace_back(name, x);
  });

  std::unordered_set<std::string> used;
  auto findDef = [&](const std::string &name) -> Stmt * {
    for (auto &[n, s] : defs)
      if (n == name && !name.empty())
        return s;
    return nullptr;
  };
  each(module, [&](Stmt *&x) {
    auto name = bound(x);
    if (name.empty())
      return;
    if (in(remove, name)) {
      x = N<SuiteStmt>();
      return;
    }
    auto def = findDef(name);
    if (!def || in(used, name))
      return;
    used.insert(name);
    if (in(patches, name)) {
      auto orig = cast<ClassStmt>(x);
      if (!orig)
        E(Error::CUSTOM, def, "overlay {}: '{}' is not a class in the module", overlayPath, name);
      // Members of the patch replace or extend those of the module's class.
      std::vector<Stmt *> added;
      each(cast<ClassStmt>(def)->getSuite(), [&](Stmt *&m) {
        auto member = bound(m);
        bool replaced = false;
        if (!member.empty())
          each(orig->getSuite(), [&](Stmt *&o) {
            if (!replaced && bound(o) == member) {
              o = m;
              replaced = true;
            }
          });
        if (!replaced)
          added.push_back(m);
      });
      for (auto *m : added)
        orig->getSuite()->addStmt(m);
    } else {
      x = def;
    }
  });
  auto suite = cast<SuiteStmt>(module);
  for (auto &[name, s] : defs)
    if (name.empty() || !in(used, name)) {
      if (in(patches, name))
        E(Error::CUSTOM, s, "overlay {}: no class '{}' in the module to patch", overlayPath, name);
      if (suite)
        suite->addStmt(s);
    }
}

} // namespace codon::ast
