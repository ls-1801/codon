// Parses a Codon program with the tokenizer and the generated token parser.
#pragma once
#include <string>
#include "codon/parser/cache.h"
#include "llvm/Support/Error.h"

namespace codon::tokparser {
llvm::Expected<ast::Stmt *> parseProgram(ast::Cache *cache, const std::string &file, const std::string &code,
                                         int lineOffset = 0);
}
