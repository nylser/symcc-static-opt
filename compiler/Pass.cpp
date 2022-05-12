// This file is part of SymCC.
//
// SymCC is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// SymCC is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// SymCC. If not, see <https://www.gnu.org/licenses/>.

#include "Pass.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/Utils/ModuleUtils.h>

#include "Runtime.h"
#include "Symbolizer.h"
#include "analyze/AnalyzePass.h"

using namespace llvm;

#ifndef NDEBUG
#define DEBUG(X)                                                               \
  do {                                                                         \
    X;                                                                         \
  } while (false)
#else
#define DEBUG(X) ((void)0)
#endif

char SymbolizePass::ID = 0;

bool SymbolizePass::doInitialization(Module &M) {
  DEBUG(errs() << "Symbolizer module init\n");

  // Redirect calls to external functions to the corresponding wrappers and
  // rename internal functions.
  for (auto &function : M.functions()) {
    auto name = function.getName();
    if (isInterceptedFunction(function))
      function.setName(name + "_symbolized");
  }

  // Insert a constructor that initializes the runtime and any globals.
  Function *ctor;
  std::tie(ctor, std::ignore) = createSanitizerCtorAndInitFunctions(
      M, kSymCtorName, "_sym_initialize", {}, {});
  appendToGlobalCtors(M, ctor, 0);

  return true;
}

bool SymbolizePass::runOnFunction(Function &F) {
  auto functionName = F.getName();
  if (functionName == kSymCtorName)
    return false;

  // DEBUG(errs() << "Symbolizing function ");
  // DEBUG(errs().write_escaped(functionName) << '\n');

  SmallVector<Instruction *, 0> allInstructions;
  SmallVector<BasicBlock *, 0> allBasicBlocks;
  allBasicBlocks.reserve(F.getBasicBlockList().size());
  for (auto &B : F.getBasicBlockList()) {
    allBasicBlocks.push_back(&B);
  }
  allInstructions.reserve(F.getInstructionCount());
  for (auto &I : instructions(F))
    allInstructions.push_back(&I);

  Symbolizer symbolizer(*F.getParent());
  symbolizer.symbolizeFunctionArguments(F);

  AnalyzePass &pass = getAnalysis<AnalyzePass>();
  FunctionAnalysisData *data = pass.getFunctionAnalysisData(F);
  assert(data != nullptr && "Analysis data is missing!");

  ValueMap<BasicBlock *, std::tuple<BasicBlock *, ValueToValueMapTy *>>
      cloneData;

  for (auto basicBlock : allBasicBlocks) {
    ValueToValueMapTy *VMap = new ValueToValueMapTy();
    auto clonedBlock = CloneBasicBlock(basicBlock, *VMap, ".easy", &F);
    // updating inner references
    for (auto &inst : clonedBlock->getInstList()) {
      for (auto &operand : inst.operands()) {
        if (auto *value = operand.get(); value != nullptr) {
          if (auto mappedValue = VMap->find(value);
              mappedValue != VMap->end()) {
            inst.setOperand(operand.getOperandNo(), mappedValue->second);
          }
        }
      }
    }
    clonedBlock->moveAfter(basicBlock);
    cloneData.insert(
        std::make_pair(basicBlock, std::make_tuple<>(clonedBlock, VMap)));
    symbolizer.insertBasicBlockNotification(*basicBlock);
  }
  for (auto *instPtr : allInstructions) {
    symbolizer.visit(instPtr);
  }
  for (auto *currentBlock : allBasicBlocks) {

    // errs() << "instPtr Parent" << *(instPtr->getParent()) << "\n";
    auto dependencies = data->basicBlockData.find(currentBlock);
    // assert(it != data->basicBlockData.end() &&
    //        "Analysis data for block is missing!");
    if (dependencies == data->basicBlockData.end())
      assert("stuff");

    auto clonedBlockData = cloneData.find(currentBlock);
    assert(clonedBlockData != cloneData.end() && "Cloned block data missing!");
    symbolizer.insertBasicBlockCheck(
        *currentBlock, *std::get<0>(clonedBlockData->second),
        *std::get<1>(clonedBlockData->second), dependencies->second);
  }

  symbolizer.finalizePHINodes();
  // symbolizer.shortCircuitExpressionUses();

  // DEBUG(errs() << F << '\n');
  verifyFunction(F, &errs());
  // assert(!verifyFunction(F, &errs()) &&
  //        "SymbolizePass produced invalid bitcode");

  return true;
}

void SymbolizePass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<AnalyzePass>();
}
