#include <llvm/ADT/SmallSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/ValueMap.h>
#include <llvm/Pass.h>

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Woverloaded-virtual"
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-variable"
#pragma clang diagnostic ignored "-Wself-assign"
#pragma clang diagnostic ignored "-Wignored-qualifiers"
#include "Graphs/SVFG.h"
#pragma clang diagnostic pop

class FunctionAnalysisData {

public:
  FunctionAnalysisData() {}
  std::map<llvm::BasicBlock *, std::list<const llvm::Value *>> basicBlockData;
  std::map<llvm::Instruction *, std::list<const llvm::Value *>>
      afterCallDependencies;
};

class AnalyzePass : public llvm::ModulePass {
public:
  static char ID;

  AnalyzePass() : ModulePass(ID) {}

  bool runOnModule(llvm::Module &M) override;

  FunctionAnalysisData *getFunctionAnalysisData(llvm::Function &F);

private:
  llvm::SmallSet<const llvm::Value *, 8>
  traversePredecessors(llvm::BasicBlock &BB, llvm::Value *Value);

  llvm::ValueMap<llvm::Value *, llvm::SmallSet<const llvm::Value *, 8>>
      valueDependencies;

  llvm::ValueMap<llvm::Function *, FunctionAnalysisData> functionAnalysisData;
  SVF::SVFG *svfg;
  SVF::VFG *vfg;
};