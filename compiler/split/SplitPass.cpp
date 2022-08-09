#include "SplitPass.h"
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

using namespace llvm;

char SplitPass::ID = 1;

bool SplitPass::runOnModule(Module &M) {
  for (auto &F : M.functions()) {
    if (F.empty() || F.getName() == kSymCtorName)
      continue;
    // errs() << "running split pass for function " << F.getName() << "\n";
    SmallVector<Instruction *, 0> instructionsToVisit;
    instructionsToVisit.reserve(F.getInstructionCount());

    for (auto &I : instructions(F)) {
      instructionsToVisit.push_back(&I);
    }

    for (auto I : instructionsToVisit) {
      if (isa<LoadInst>(I) || isa<CallInst>(I)) {
        auto nextInst = I->getNextNode();
        auto basicBlock = I->getParent();
        assert(nextInst != nullptr && nextInst->getParent() == basicBlock &&
               "load or call inst should never be the last instruction in a "
               "basic block, "
               "right?");
        SplitBlock(basicBlock, nextInst, nullptr, nullptr, nullptr);
      }
    }
  }
  return true;
};
