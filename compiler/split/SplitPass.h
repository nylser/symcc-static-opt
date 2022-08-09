#include <llvm/Pass.h>

class SplitPass : public llvm::ModulePass {
public:
  static char ID;

  SplitPass() : ModulePass(ID) {}

  bool runOnModule(llvm::Module &M) override;

private:
  static constexpr char kSymCtorName[] = "__sym_ctor";
};