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
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
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

  errs() << "============" << functionName << "============\n";
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
  DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  FunctionAnalysisData *data = pass.getFunctionAnalysisData(F);
  assert(data != nullptr && "Analysis data is missing!");

  ValueMap<BasicBlock *, SplitData> splitData;

  for (auto basicBlock : allBasicBlocks) {
    auto anaDataIt = data->basicBlockData.find(basicBlock);
    assert(anaDataIt != data->basicBlockData.end());
    if (anaDataIt->second.empty()) {
      symbolizer.insertBasicBlockNotification(*basicBlock);
    } else {
      auto data = symbolizer.splitIntoBlocks(*basicBlock);
      splitData.insert(std::make_pair(basicBlock, data));
      symbolizer.insertBasicBlockNotification(*data.getSymbolizedBlock());
    }
  }

  for (auto *instPtr : allInstructions) {
    symbolizer.visit(instPtr);
  }

  ValueMap<Value *, Instruction *> symbolicMerges;

  for (auto *currentBlock : allBasicBlocks) {

    // errs() << "instPtr Parent" << *(instPtr->getParent()) << "\n";
    auto dependenciesIt = data->basicBlockData.find(currentBlock);
    // assert(it != data->basicBlockData.end() &&
    //        "Analysis data for block is missing!");
    assert(dependenciesIt != data->basicBlockData.end() &&
           "Dependencies for block are non-existant");

    if (dependenciesIt->second.empty())
      continue;

    auto blockSplitDataIt = splitData.find(currentBlock);

    assert(blockSplitDataIt != splitData.end() && "Cloned block data missing!");
    auto blockSplitData = blockSplitDataIt->second;

    symbolizer.finalizeTerminators(blockSplitData);

    for (auto *instPtr : blockSplitData.storesToInstrument) {
      // errs() << "instrumenting store in easy block " << *instPtr << "\n";
      symbolizer.visitStore(*instPtr);
    }

    // recalculate Dominator tree
    DT.recalculate(F);

    symbolizer.insertBasicBlockCheck(blockSplitData, dependenciesIt->second,
                                     symbolicMerges, DT);
    symbolizer.populateMergeBlock(blockSplitData, symbolicMerges);

    symbolizer.cleanUpSuccessorPHINodes(blockSplitData, symbolicMerges);

    if (blockSplitData.getEasyBlock()->hasNPredecessors(0)) {
      blockSplitData.getEasyBlock()->removeFromParent();
    }
    // if merge block doesnt have any predecessors, we can remove it
    if (blockSplitData.getMergeBlock()->hasNPredecessors(0)) {
      blockSplitData.getMergeBlock()->removeFromParent();
    }
  }
  DT.recalculate(F);
  ///  TODO: do we still need this? Answer: right now, we do. It creates value
  ///  expressions for otherwise concrete values
  symbolizer.shortCircuitExpressionUses(symbolicMerges, DT);
  symbolizer.finalizePHINodes(symbolicMerges);
  DT.recalculate(F);
  auto *mod = F.getParent();
  auto &context = mod->getContext();
  Type *intType = Type::getInt32Ty(context);
  std::vector<Type *> printfArgsTypes({Type::getInt8PtrTy(context)});
  FunctionType *printfType = FunctionType::get(intType, printfArgsTypes, true);
  auto printfFunc = mod->getOrInsertFunction("printf", printfType);

  IRBuilder<> builder(F.getEntryBlock().getFirstNonPHI());
  // auto str = builder.CreateGlobalStringPtr("easy execution\n");

  std::set<PHINode *> toRemove;
  for (auto pair : splitData) {
    auto blockSplitData = pair->second;
    auto easyBlock = blockSplitData.getEasyBlock();
    IRBuilder<> IRB(easyBlock->getFirstNonPHI());
    // The format string for the printf function, declared as a global literal
    auto str = builder.CreateGlobalStringPtr(
        "easy execution of " + blockSplitData.getCheckBlock()->getName().str() +
        "\n");
    IRB.CreateCall(printfFunc, {str}, "printf");
    auto mergeBlock = blockSplitData.getMergeBlock();
    for (auto &phi : mergeBlock->phis()) {
      for (auto &incoming : phi.incoming_values()) {
        if (incoming.get() == nullptr)
          continue;
        auto incomingInst = dyn_cast<Instruction>(incoming.get());
        if (incomingInst == nullptr)
          continue;
        if (!DT.dominates(incomingInst,
                          phi.getIncomingBlock(incoming.getOperandNo())
                              ->getTerminator())) {
          errs() << *incomingInst << " doesn't dominate "
                 << phi.getIncomingBlock(incoming.getOperandNo())->getName()
                 << "\n";
          if (phi.isSafeToRemove())
            toRemove.insert(&phi);
        }
      }
    }
  }
  for (auto phi : toRemove) {
    phi->removeFromParent();
    phi->dropAllReferences();
  }

  // DEBUG(errs() << F << '\n');
  verifyFunction(F, &errs());
  // assert(!verifyFunction(F, &errs()) &&
  //        "SymbolizePass produced invalid bitcode");
  errs() << "------------" << F.getName() << "------------\n";
  return true;
}

void SymbolizePass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<AnalyzePass>();
}
