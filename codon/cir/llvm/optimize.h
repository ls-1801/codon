// Copyright (C) 2022-2026 Exaloop Inc. <https://exaloop.io>

#pragma once

#include <memory>

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

void optimize(llvm::Module *module, bool debug, bool jit = false,
              PluginManager *plugins = nullptr);

bool isFastMathOn();
} // namespace ir
} // namespace codon
