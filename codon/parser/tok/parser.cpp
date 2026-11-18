#include "codon/parser/tok/parser.h"
#include "codon/parser/tok/grammar.inc"
#include "codon/compiler/error.h"

namespace codon::tokparser {

llvm::Expected<ast::Stmt *> parseProgram(ast::Cache *cache, const std::string &file, const std::string &code,
                                         int lineOffset) {
  auto tokens = tok::tokenize(code);
  if (!tokens.error.empty())
    return llvm::make_error<error::ParserErrorInfo>(
        ErrorMessage(tokens.error, SrcInfo(file, int(tokens.errorLine) + lineOffset, int(tokens.errorCol), 0)));
  Parser parser(code, tokens.tokens, ParseContext{cache, file, lineOffset, 0});
  try {
    auto result = parser.r_program();
    if (result)
      return *result;
  } catch (const ParseError &e) {
    return llvm::make_error<error::ParserErrorInfo>(
        ErrorMessage(e.message, SrcInfo(file, int(e.at->line) + lineOffset, int(e.at->col), 0)));
  }
  const auto &t = tokens.tokens[std::min(parser.maxPos, tokens.tokens.size() - 1)];
  std::string unexpected = t.kind == tok::Kind::EndMarker ? "end of input"
                           : t.kind == tok::Kind::Newline ? "end of line"
                           : t.kind == tok::Kind::Indent  ? "indentation"
                           : t.kind == tok::Kind::Dedent  ? "dedent"
                                                          : "'" + std::string(parser.text(&t)) + "'";
  return llvm::make_error<error::ParserErrorInfo>(
      ErrorMessage("syntax error, unexpected " + unexpected, SrcInfo(file, int(t.line) + lineOffset, int(t.col), 0)));
}

} // namespace codon::tokparser
