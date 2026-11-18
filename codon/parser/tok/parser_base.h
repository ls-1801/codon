// Runtime of the generated token parser (generate.py): token matching, source positions and the parse context.
#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "codon/parser/tok/tokenizer.h"
#include "codon/parser/ast.h"
#include "codon/parser/cache.h"
#include "codon/parser/common.h"

namespace codon::tokparser {

using tok::Kind;
using tok::Token;

/// An error that an action reports, e.g. an invalid escape in a string.
struct ParseError {
  std::string message;
  const Token *at;
};

struct ParseContext {
  ast::Cache *cache;
  std::string file;
  int line_offset = 0;
  int col_offset = 0;

  bool hasCustomStmtKeyword(const std::string &kwd, bool hasExpr) const {
    auto i = cache->customBlockStmts.find(kwd);
    return i != cache->customBlockStmts.end() && i->second.first == hasExpr;
  }
  bool hasCustomExprStmt(const std::string &kwd) const {
    return cache->customExprStmts.find(kwd) != cache->customExprStmts.end();
  }
};

/// The hard keywords of Codon's grammar: they are never a NAME.
inline bool isHardKeyword(std::string_view s) {
  static const std::unordered_map<std::string_view, bool> keywords{
      {"False", true}, {"else", true},     {"import", true}, {"pass", true},  {"None", true},
      {"break", true}, {"except", true},   {"in", true},     {"raise", true}, {"True", true},
      {"class", true}, {"finally", true},  {"is", true},     {"return", true}, {"and", true},
      {"continue", true}, {"for", true},   {"as", true},     {"lambda", true}, {"try", true},
      {"def", true},   {"from", true},     {"while", true},  {"assert", true}, {"del", true},
      {"global", true}, {"not", true},     {"with", true},   {"elif", true},  {"if", true},
      {"or", true},    {"yield", true},    {"async", true},  {"await", true}};
  return keywords.contains(s);
}

/// A memoized result at a token position: end is the position after the match plus one, 0 if not yet parsed there.
template <typename T> struct MemoEntry {
  uint32_t end = 0;
  std::optional<T> value;
};

struct ParserBase {
  std::string_view src;
  const std::vector<Token> &toks;
  size_t pos = 0;
  size_t maxPos = 0; // the furthest token a match failed at, for the error message
  ParseContext CTX;

  ParserBase(std::string_view src, const std::vector<Token> &toks, ParseContext ctx)
      : src(src), toks(toks), CTX(std::move(ctx)) {}

  static std::optional<const Token *> tokOpt(const Token *t) {
    return t ? std::optional<const Token *>(t) : std::nullopt;
  }

  std::string_view text(const Token *t) const { return src.substr(t->start, t->end - t->start); }
  std::string str(const Token *t) const { return std::string(text(t)); }

  void miss() {
    if (pos > maxPos)
      maxPos = pos;
  }

  const Token *expectKind(Kind kind) {
    if (pos < toks.size() && toks[pos].kind == kind)
      return &toks[pos++];
    miss();
    return nullptr;
  }
  const Token *expectOp(std::string_view s) {
    if (pos < toks.size() && toks[pos].kind == Kind::Op && text(&toks[pos]) == s)
      return &toks[pos++];
    miss();
    return nullptr;
  }
  const Token *expectKeyword(std::string_view s) {
    if (pos < toks.size() && toks[pos].kind == Kind::Name && text(&toks[pos]) == s)
      return &toks[pos++];
    miss();
    return nullptr;
  }
  const Token *expectName() {
    if (pos < toks.size() && toks[pos].kind == Kind::Name && !isHardKeyword(text(&toks[pos])))
      return &toks[pos++];
    miss();
    return nullptr;
  }
  /// Whitespace precedes the next token.
  bool sp() const { return pos < toks.size() && toks[pos].spaceBefore; }

  /// The source position of the tokens from start to the current position.
  SrcInfo loc(size_t start) const {
    const Token &first = toks[start < toks.size() ? start : toks.size() - 1];
    uint32_t end = pos > start ? toks[pos - 1].end : first.start;
    return SrcInfo(CTX.file, int(first.line) + CTX.line_offset, int(first.col) + CTX.col_offset,
                   int(end - first.start));
  }
};

} // namespace codon::tokparser
