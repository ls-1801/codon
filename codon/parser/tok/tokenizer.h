// Tokenizer for Codon source, for a token-based parser of Codon's grammar (codon/parser/peg/grammar.peg).
//
// It follows CPython's tokenizer: NEWLINE ends a logical line, INDENT and DEDENT follow the indentation, and lines are
// joined inside brackets and after a backslash. Codon additions:
// - The body of a function decorated with @llvm or @python is raw text: one EXTERN token.
// - "## codon: name = value" is a DIRECTIVE token; other comments are skipped.
// - Each token records whether whitespace precedes it, as the grammar distinguishes e.g. `print x` from `print(x)` and
//   `10u` from `10 u`.
// - "1...5" is NUMBER ELLIPSIS NUMBER, not FLOAT "1." and ".5".
#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace codon::tok {

enum class Kind : uint8_t {
  EndMarker,
  Newline,
  Indent,
  Dedent,
  Name,
  Number,
  String, // with its prefix and quotes, e.g. r"..." or """..."""
  Op,
  Directive, // "## codon: ..." comment
  Extern,    // raw body of an @llvm / @python function
  Error,
};

struct Token {
  Kind kind;
  bool spaceBefore; // whitespace, a comment or a joined line precedes the token
  uint32_t start;   // byte offset in the source
  uint32_t end;
  uint32_t line; // 1-based
  uint32_t col;  // 1-based
};

struct TokenizeResult {
  std::vector<Token> tokens;
  std::string error; // empty on success
  uint32_t errorLine = 0, errorCol = 0;
};

TokenizeResult tokenize(std::string_view source);

const char *kindName(Kind kind);

} // namespace codon::tok
