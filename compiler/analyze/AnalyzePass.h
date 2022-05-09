#include <llvm/IR/Module.h>
#include <llvm/IR/ValueMap.h>
#include <llvm/IR/Function.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Value.h>
#include <llvm/Pass.h>

#include "Graphs/SVFG.h"

class AnalyzePass : public llvm::FunctionPass
{
public:
    static char ID;

    AnalyzePass() : FunctionPass(ID) {}

    bool doInitialization(llvm::Module &M) override;
    bool runOnFunction(llvm::Function &F) override;
    bool doFinalization(llvm::Module &M) override;

    llvm::ValueMap<llvm::BasicBlock *, std::string *> *getFunctionAnalysisData(llvm::Function &F);

private:
    llvm::Value *traversePredecessors(llvm::BasicBlock &BB, llvm::Value *Value);

    llvm::ValueMap<llvm::Function *, llvm::ValueMap<llvm::BasicBlock *, std::string *> *> functionAnalysisData;
    SVF::SVFG *svfg;
    SVF::VFG *vfg;
};