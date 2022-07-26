#include <llvm/Pass.h>

class SplitPass : public llvm::ModulePass {
public:
  static char ID;

  SplitPass() : ModulePass(ID) {}

  bool runOnModule(llvm::Module &M) override;
  void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
};