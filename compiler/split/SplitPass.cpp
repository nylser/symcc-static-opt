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
    if (F.empty())
      continue;
    // errs() << "running split pass for function " << F.getName() << "\n";
    for (auto &I : instructions(F)) {
      auto loadInst = dyn_cast<LoadInst>(&I);
      if (loadInst == nullptr)
        continue;

      auto nextInst = I.getNextNode();
      auto basicBlock = I.getParent();
      assert(nextInst != nullptr && nextInst->getParent() == basicBlock &&
             "load inst should never be the last instruction in a basic block, "
             "right?");
      SplitBlock(basicBlock, nextInst, nullptr, nullptr, nullptr,
                 loadInst->getParent()->getName() + ".loadSplit");
    }
    continue;
  }
  return true;
};
