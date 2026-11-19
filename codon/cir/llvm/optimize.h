// Copyright (C) 2022-2026 Exaloop Inc. <https://exaloop.io>

#pragma once

#include <memory>
#include <string>

#include "codon/cir/llvm/llvm.h"
#include "codon/dsl/plugins.h"

namespace codon {
namespace ir {
std::unique_ptr<llvm::TargetMachine>
getTargetMachine(llvm::Triple triple, llvm::StringRef cpuStr,
                 llvm::StringRef featuresStr, const llvm::TargetOptions &options,
                 bool pic = false);

std::unique_ptr<llvm::TargetMachine>
getTargetMachine(llvm::Module *module, bool setFunctionAttributes = false,
                 bool pic = false);

/// Enables or disables architecture-specific LLVM optimizations.
void setNativeOptimizationEnabled(bool enabled);

struct LLVMOptimizationOptions {
  llvm::OptimizationLevel level = llvm::OptimizationLevel::O3;
  unsigned runs = 2;
  bool preserveDebugInfo = false;
  bool preserveDebugStackFrames = false;
  bool jit = false;
  /// Add Codon's passes (allocation removal and hoisting, coroutine branch
  /// simplification) to the standard pipeline.
  bool codonPasses = true;
  /// A pass pipeline in LLVM's textual form (as for `opt -passes=`) that replaces the
  /// standard pipeline of `level`. Codon's passes are available in it as
  /// `codon-alloc-remover`, `codon-alloc-hoister` (function passes) and
  /// `codon-coro-branch-simplifier` (a loop pass).
  std::string pipeline;

  static LLVMOptimizationOptions debug() {
    return {
        .level = llvm::OptimizationLevel::O0,
        .runs = 1,
        .preserveDebugInfo = true,
        .preserveDebugStackFrames = true,
        .jit = false,
    };
  }

  static LLVMOptimizationOptions release() {
    return {
        .level = llvm::OptimizationLevel::O3,
        .runs = 2,
        .preserveDebugInfo = false,
        .preserveDebugStackFrames = false,
        .jit = false,
    };
  }
};

void optimize(llvm::Module *module, const LLVMOptimizationOptions &options,
              PluginManager *plugins = nullptr);

/// Adds Codon's passes to a pass builder: by name for textual pipelines, and, if
/// `extensionPoints`, at the extension points where Codon's own pipeline runs them. For
/// compilers that optimize Codon's LLVM IR in a pipeline of their own.
void registerCodonLLVMPasses(llvm::PassBuilder &pb, bool extensionPoints = true);

void optimize(llvm::Module *module, bool debug, bool jit = false,
              PluginManager *plugins = nullptr);

bool isFastMathOn();
} // namespace ir
} // namespace codon
