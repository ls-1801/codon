#include "codon/parser/tok/tokenizer.h"

#include <cstring>

namespace codon::tok {
namespace {

bool isNameStart(char c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'; }
bool isNameChar(char c) { return isNameStart(c) || (c >= '0' && c <= '9'); }
bool isDigit(char c) { return c >= '0' && c <= '9'; }
bool isHexDigit(char c) {
  return isDigit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}

// Operators, longest first within each length.
constexpr const char *ops3[] = {"**=", "//=", ">>=", "<<=", "...", "||>"};
constexpr const char *ops2[] = {"|>", "->", ":=", "**", "//", "<<", ">>", "<=", ">=", "==", "!=",
                                "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "@="};
constexpr const char ops1[] = "()[]{},:;.@=+-*/%&|^~<>!";

class Tokenizer {
public:
  explicit Tokenizer(std::string_view s) : s(s) {}

  TokenizeResult run() {
    indents.push_back(0);
    while (true) {
      if (atLineStart && parens == 0) {
        if (!startLine())
          break;
        continue;
      }
      if (pos >= s.size()) {
        endOfInput();
        break;
      }
      char c = s[pos];
      if (c == ' ' || c == '\t' || c == '\f') {
        ++pos;
        space = true;
        continue;
      }
      if (c == '\r' || c == '\n') {
        if (parens > 0) {
          space = true;
        } else {
          if (lineHasTokens)
            emit(Kind::Newline, pos, pos);
          atLineStart = true;
        }
        skipEol();
        continue;
      }
      if (c == '#' && !(lineHasTokens == false && isDirective(pos))) {
        while (pos < s.size() && s[pos] != '\r' && s[pos] != '\n')
          ++pos;
        space = true;
        continue;
      }
      if (c == '\\' && pos + 1 < s.size() && (s[pos + 1] == '\n' || s[pos + 1] == '\r')) {
        ++pos;
        skipEol();
        space = true;
        continue;
      }
      if (!token())
        break;
    }
    return std::move(result);
  }

private:
  std::string_view s;
  size_t pos = 0;
  uint32_t line = 1;
  size_t lineStart = 0;
  int parens = 0;
  bool atLineStart = true;
  bool space = false;
  bool lineHasTokens = false;
  std::vector<size_t> indents;
  TokenizeResult result;

  // @llvm / @python functions: the decorator line sets externDecorator; a following def header line sets externBody.
  bool externDecorator = false;
  bool externBody = false;
  size_t lineFirstToken = 0;

  uint32_t col(size_t at) const { return uint32_t(at - lineStart + 1); }

  void emit(Kind kind, size_t start, size_t end) {
    bool layout = kind == Kind::Indent || kind == Kind::Dedent;
    if (!lineHasTokens && !layout)
      lineFirstToken = result.tokens.size();
    result.tokens.push_back(Token{kind, space, uint32_t(start), uint32_t(end), line, col(start)});
    space = false;
    if (!layout)
      lineHasTokens = kind != Kind::Newline;
    if (kind == Kind::Newline)
      endLogicalLine();
  }

  bool error(const std::string &msg, size_t at) {
    result.error = msg;
    result.errorLine = line;
    result.errorCol = col(at);
    return false;
  }

  void skipEol() {
    if (s[pos] == '\r' && pos + 1 < s.size() && s[pos + 1] == '\n')
      ++pos;
    ++pos;
    ++line;
    lineStart = pos;
  }

  // A logical line ended: track @llvm / @python decorators and the header of the function they decorate.
  void endLogicalLine() {
    auto &t = result.tokens;
    size_t first = lineFirstToken, last = t.size() - 1; // last is the NEWLINE
    auto text = [&](size_t i) { return s.substr(t[i].start, t[i].end - t[i].start); };
    bool isDecorator = first < last && t[first].kind == Kind::Op && text(first) == "@";
    if (isDecorator && last - first == 2 && t[first + 1].kind == Kind::Name &&
        (text(first + 1) == "llvm" || text(first + 1) == "python")) {
      externDecorator = true;
      return;
    }
    if (externDecorator && isDecorator)
      return;
    if (externDecorator) {
      size_t def = first;
      if (t[def].kind == Kind::Name && text(def) == "async")
        ++def;
      externBody = def < last && t[def].kind == Kind::Name && text(def) == "def" &&
                   t[last - 1].kind == Kind::Op && text(last - 1) == ":";
    }
    externDecorator = false;
  }

  // At the start of a physical line outside brackets: blank and comment lines, indentation, raw @llvm bodies.
  bool startLine() {
    size_t indentStart = pos;
    while (pos < s.size() && (s[pos] == ' ' || s[pos] == '\t' || s[pos] == '\f'))
      ++pos;
    size_t width = pos - indentStart;
    if (pos >= s.size()) {
      atLineStart = false;
      return true;
    }
    char c = s[pos];
    if (c == '\r' || c == '\n') {
      skipEol();
      return true;
    }
    if (c == '#' && !isDirective(pos)) {
      while (pos < s.size() && s[pos] != '\r' && s[pos] != '\n')
        ++pos;
      if (pos < s.size())
        skipEol();
      return true;
    }
    if (externBody) {
      externBody = false;
      if (width > indents.back()) {
        externBlock(indentStart, width);
        return true;
      }
    }
    if (width > indents.back()) {
      indents.push_back(width);
      emit(Kind::Indent, pos, pos);
    } else {
      while (width < indents.back()) {
        indents.pop_back();
        emit(Kind::Dedent, pos, pos);
      }
      if (width != indents.back())
        return error("unexpected dedent", pos);
    }
    atLineStart = false;
    space = false;
    return true;
  }

  // The raw body of an @llvm / @python function: from its first line, all lines indented at least as much, and blank
  // lines among and after them, as Codon's extern rule takes them.
  void externBlock(size_t blockStart, size_t width) {
    size_t p = blockStart;
    uint32_t startLineNo = line;
    size_t end = blockStart;
    uint32_t endLine = line;
    size_t endLineStart = lineStart;
    while (p < s.size()) {
      size_t q = p;
      while (q < s.size() && (s[q] == ' ' || s[q] == '\t'))
        ++q;
      bool blank = q >= s.size() || s[q] == '\r' || s[q] == '\n';
      if (!blank && q - p < width)
        break;
      while (q < s.size() && s[q] != '\r' && s[q] != '\n')
        ++q;
      if (q < s.size()) {
        if (s[q] == '\r' && q + 1 < s.size() && s[q + 1] == '\n')
          ++q;
        ++q;
      }
      p = q;
      ++endLine;
      endLineStart = p;
      end = p;
    }
    result.tokens.push_back(
        Token{Kind::Extern, true, uint32_t(blockStart), uint32_t(end), startLineNo, 1});
    pos = end;
    line = endLine;
    lineStart = endLineStart;
    atLineStart = true;
    lineHasTokens = false;
  }

  // "## codon: name = value"
  bool isDirective(size_t p) const {
    if (s.substr(p, 2) != "##")
      return false;
    p += 2;
    auto skip = [&] {
      while (p < s.size() && (s[p] == ' ' || s[p] == '\t'))
        ++p;
    };
    skip();
    if (s.substr(p, 6) != "codon:")
      return false;
    return true;
  }

  void endOfInput() {
    if (lineHasTokens)
      emit(Kind::Newline, pos, pos);
    while (indents.size() > 1) {
      indents.pop_back();
      emit(Kind::Dedent, pos, pos);
    }
    emit(Kind::EndMarker, pos, pos);
  }

  bool token() {
    size_t start = pos;
    char c = s[pos];
    if (c == '#') { // a directive at the start of a statement
      while (pos < s.size() && s[pos] != '\r' && s[pos] != '\n')
        ++pos;
      emit(Kind::Directive, start, pos);
      return true;
    }
    if (isNameStart(c)) {
      while (pos < s.size() && isNameChar(s[pos]))
        ++pos;
      if (pos < s.size() && (s[pos] == '"' || s[pos] == '\''))
        return string(start);
      emit(Kind::Name, start, pos);
      return true;
    }
    if (c == '"' || c == '\'')
      return string(start);
    if (isDigit(c) || (c == '.' && pos + 1 < s.size() && isDigit(s[pos + 1])))
      return number(start);
    if (static_cast<unsigned char>(c) >= 0x80)
      return error("unexpected non-ASCII character", pos);
    for (auto *op : ops3)
      if (s.substr(pos, 3) == op) {
        pos += 3;
        emit(Kind::Op, start, pos);
        return true;
      }
    for (auto *op : ops2)
      if (s.substr(pos, 2) == op) {
        pos += 2;
        emit(Kind::Op, start, pos);
        return true;
      }
    if (std::strchr(ops1, c)) {
      if (c == '(' || c == '[' || c == '{')
        ++parens;
      else if ((c == ')' || c == ']' || c == '}') && parens > 0)
        --parens;
      ++pos;
      emit(Kind::Op, start, pos);
      return true;
    }
    return error(std::string("unexpected character '") + c + "'", pos);
  }

  // A string literal; start is at its prefix or at its quote.
  bool string(size_t start) {
    char q = s[pos];
    bool triple = s.substr(pos, 3) == std::string(3, q);
    pos += triple ? 3 : 1;
    while (true) {
      if (pos >= s.size())
        return error("unterminated string", start);
      char c = s[pos];
      if (c == '\\' && pos + 1 < s.size()) {
        if (s[pos + 1] == '\n') {
          pos += 2;
          ++line;
          lineStart = pos;
        } else {
          pos += 2;
        }
        continue;
      }
      if (triple) {
        if (s.substr(pos, 3) == std::string(3, q)) {
          pos += 3;
          break;
        }
        if (c == '\n') {
          ++pos;
          ++line;
          lineStart = pos;
          continue;
        }
      } else {
        if (c == q) {
          ++pos;
          break;
        }
        if (c == '\n' || c == '\r')
          return error("unterminated string", start);
      }
      ++pos;
    }
    // The token starts on the line where the string starts.
    result.tokens.push_back(Token{Kind::String, space, uint32_t(start), uint32_t(pos), startLineOf(start),
                                  startColOf(start)});
    if (!lineHasTokens)
      lineFirstToken = result.tokens.size() - 1;
    space = false;
    lineHasTokens = true;
    return true;
  }

  uint32_t startLineOf(size_t at) const {
    // Strings spanning lines: count back. Most strings are on one line.
    uint32_t l = line;
    for (size_t i = at; i < lineStart; ++i)
      if (s[i] == '\n')
        --l;
    return at >= lineStart ? line : l;
  }
  uint32_t startColOf(size_t at) const {
    size_t ls = at;
    while (ls > 0 && s[ls - 1] != '\n')
      --ls;
    return uint32_t(at - ls + 1);
  }

  // Numbers as Codon's grammar reads them: BININT, HEXINT, DECINT, PTFLOAT, EXPFLOAT. A suffix such as the u of 10u is a
  // separate Name token without space before it.
  bool number(size_t start) {
    auto digits = [&](auto pred) {
      while (pos < s.size() && (pred(s[pos]) || (s[pos] == '_' && pos + 1 < s.size() && pred(s[pos + 1]))))
        ++pos;
    };
    if (s[pos] == '0' && pos + 2 < s.size() && (s[pos + 1] == 'x' || s[pos + 1] == 'X') && isHexDigit(s[pos + 2])) {
      pos += 2;
      digits(isHexDigit);
      emit(Kind::Number, start, pos);
      return true;
    }
    if (s[pos] == '0' && pos + 2 < s.size() && (s[pos + 1] == 'b' || s[pos + 1] == 'B') &&
        (s[pos + 2] == '0' || s[pos + 2] == '1')) {
      pos += 2;
      auto bin = [](char c) { return c == '0' || c == '1'; };
      while (pos < s.size() && (bin(s[pos]) || s[pos] == '_'))
        ++pos;
      emit(Kind::Number, start, pos);
      return true;
    }
    digits(isDigit);
    // "1...5" is a range: the number ends before "...".
    if (pos < s.size() && s[pos] == '.' && s.substr(pos, 3) != "...") {
      ++pos;
      digits(isDigit);
    }
    if (pos < s.size() && (s[pos] == 'e' || s[pos] == 'E')) {
      size_t p = pos + 1;
      if (p < s.size() && (s[p] == '+' || s[p] == '-'))
        ++p;
      if (p < s.size() && isDigit(s[p])) {
        pos = p;
        digits(isDigit);
      }
    }
    emit(Kind::Number, start, pos);
    return true;
  }
};

} // namespace

TokenizeResult tokenize(std::string_view source) { return Tokenizer(source).run(); }

const char *kindName(Kind kind) {
  switch (kind) {
  case Kind::EndMarker: return "ENDMARKER";
  case Kind::Newline: return "NEWLINE";
  case Kind::Indent: return "INDENT";
  case Kind::Dedent: return "DEDENT";
  case Kind::Name: return "NAME";
  case Kind::Number: return "NUMBER";
  case Kind::String: return "STRING";
  case Kind::Op: return "OP";
  case Kind::Directive: return "DIRECTIVE";
  case Kind::Extern: return "EXTERN";
  case Kind::Error: return "ERROR";
  }
  return "?";
}

} // namespace codon::tok
