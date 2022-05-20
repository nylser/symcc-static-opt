#include "AnalyzePass.h"

#include <llvm/IR/Argument.h>
#include <llvm/IR/User.h>
#include <llvm/Support/raw_ostream.h>

#include "SVF-FE/LLVMUtil.h"
#include "SVF-FE/PAGBuilder.h"
#include "Util/Options.h"
#include "Util/SVFModule.h"
#include "WPA/Andersen.h"

using namespace llvm;
using namespace SVF;

char AnalyzePass::ID = 0;

bool AnalyzePass::doInitialization(Module &M) {
  errs() << "initializing analyze pass: " << M.getName() << "\n";
  SVFModule *svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(M);
  svfModule->buildSymbolTableInfo();

  /// Build Program Assignment Graph (PAG)
  PAGBuilder builder;
  PAG *pag = builder.build(svfModule);

  /// Create Andersen's pointer analysis
  Andersen *ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

  /// Call Graph
  PTACallGraph *callgraph = ander->getPTACallGraph();

  /// ICFG
  ICFG *icfg = pag->getICFG();

  /// Value-Flow Graph (VFG)
  vfg = new VFG(callgraph);

  /// Sparse value-flow graph (SVFG)
  SVFGBuilder svfBuilder;
  svfg = svfBuilder.buildFullSVFGWithoutOPT(ander);
  return false;
}

bool AnalyzePass::doFinalization(llvm::Module &M) {
  // clean up memory
  delete vfg;
  delete svfg;
  AndersenWaveDiff::releaseAndersenWaveDiff();
  PAG::releasePAG();

  return false;
}

bool AnalyzePass::runOnModule(Module &M) {
  for (Function &F : M.getFunctionList()) {
    FunctionAnalysisData *data = &functionAnalysisData[&F];
    errs() << "getting function: " << F.getName() << "\n";
    for (BasicBlock &B : F)

    /**
     * @brief For each basic block I want to get the most simplified and
     * summarized values that need to be concreteness-checked. This means on
     * each used operand for instructions such as add, div, mul needs to be
     * checked with the value-flow tree But as we want to check it for this
     * basic block, we basically need to find the first dependency that is
     * defined in the same function outside the basic block or still inside said
     * basic block?
     */
    {
      SmallSet<Value *, 8> basicBlockDeps;
      errs() << B.getName() << "\n";
      for (Instruction &I : B) {
        if (auto *loadInst = dyn_cast<LoadInst>(&I)) {
          basicBlockDeps.insert(&I);
          continue;
        }

        if (auto *storeInst = dyn_cast<StoreInst>(&I)) {
          // for the store instruction, only the value that is stored actually
          // matters?
          basicBlockDeps.insert(storeInst->getOperand(0));
          continue;
        }

        for (Use &U : I.operands()) {
          if (dyn_cast<BasicBlock>(U.get()) || dyn_cast<Constant>(U.get())) {
            continue;
          }
          basicBlockDeps.insert(U.get()); // collect all operands
        }
      }

      llvm::SmallSet<const Value *, 8> basicBlockTopLevelDeps;
      for (Value *Dep : basicBlockDeps) {
        auto topLevel = traversePredecessors(B, Dep);
        valueDependencies.insert(std::make_pair(Dep, topLevel));
        basicBlockTopLevelDeps.insert(topLevel.begin(), topLevel.end());
        // errs() << *Dep << "\n";
      }

      std::list<const Value *> *topLevelDepsList = &data->basicBlockData[&B];

      for (auto *topLevelDep : basicBlockTopLevelDeps) {
        topLevelDepsList->push_back(topLevelDep);
        errs() << "Dep: " << *topLevelDep << "\n";
      }
    }

    errs() << "EndOfFunction\n\n";
  }

  return false;
}

const SVF::PAGNode *getLHSTopLevPtr(const VFGNode *);

llvm::SmallSet<const llvm::Value *, 8>
AnalyzePass::traversePredecessors(llvm::BasicBlock &BB, llvm::Value *Value) {
  auto it = valueDependencies.find(Value);
  if (it != valueDependencies.end()) {
    errs() << "short circuit!\n";
    return it->second;
  }
  llvm::SmallSet<const llvm::Value *, 8> topLevel;
  SVF::PAG *pag = PAG::getPAG();
  SVF::FIFOWorkList<const VFGNode *> worklist;
  if (dyn_cast<Constant>(Value)) {
    return topLevel;
  }
  SVF::PAGNode *pNode = pag->getPAGNode(pag->getValueNode(Value));
  const VFGNode *vNode = svfg->getDefSVFGNode(pNode);
  worklist.push(vNode);

  while (!worklist.empty()) {
    auto *currentNode = worklist.pop();
    auto *pagNode = getLHSTopLevPtr(currentNode);
    if (pagNode != nullptr) {
      const llvm::Value *nodeValue = pagNode->getValue();
      if (auto *param = dyn_cast<llvm::Argument>(nodeValue)) {
        topLevel.insert(param);
        continue;
      }
      if (auto *inst = dyn_cast<llvm::Instruction>(nodeValue)) {
        if (auto *alloca = dyn_cast<llvm::AllocaInst>(inst)) {
          // TODO: skip alloca instructions => pointers are always concretized?
          continue;
        }
        if (inst->getParent() != &BB) {
          topLevel.insert(inst);
          continue;
        }
      }
    }

    for (auto *edge : currentNode->getInEdges()) {
      worklist.push(edge->getSrcNode());
    }
  }
  return topLevel;
}

/*!
 * Copied from SVF, so that we can not crash when encountering
 * Given a VFG node, return its left hand side doesnt have a top level ptr
 */
const SVF::PAGNode *getLHSTopLevPtr(const VFGNode *node) {

  if (const AddrVFGNode *addr = SVFUtil::dyn_cast<AddrVFGNode>(node))
    return addr->getPAGDstNode();
  else if (const CopyVFGNode *copy = SVFUtil::dyn_cast<CopyVFGNode>(node))
    return copy->getPAGDstNode();
  else if (const GepVFGNode *gep = SVFUtil::dyn_cast<GepVFGNode>(node))
    return gep->getPAGDstNode();
  else if (const LoadVFGNode *load = SVFUtil::dyn_cast<LoadVFGNode>(node))
    return load->getPAGDstNode();
  else if (const PHIVFGNode *phi = SVFUtil::dyn_cast<PHIVFGNode>(node))
    return phi->getRes();
  else if (const CmpVFGNode *cmp = SVFUtil::dyn_cast<CmpVFGNode>(node))
    return cmp->getRes();
  else if (const BinaryOPVFGNode *bop =
               SVFUtil::dyn_cast<BinaryOPVFGNode>(node))
    return bop->getRes();
  else if (const UnaryOPVFGNode *uop = SVFUtil::dyn_cast<UnaryOPVFGNode>(node))
    return uop->getRes();
  else if (const ActualParmVFGNode *ap =
               SVFUtil::dyn_cast<ActualParmVFGNode>(node))
    return ap->getParam();
  else if (const FormalParmVFGNode *fp =
               SVFUtil::dyn_cast<FormalParmVFGNode>(node))
    return fp->getParam();
  else if (const ActualRetVFGNode *ar =
               SVFUtil::dyn_cast<ActualRetVFGNode>(node))
    return ar->getRev();
  else if (const FormalRetVFGNode *fr =
               SVFUtil::dyn_cast<FormalRetVFGNode>(node))
    return fr->getRet();
  else if (const NullPtrVFGNode *nullVFG =
               SVFUtil::dyn_cast<NullPtrVFGNode>(node))
    return nullVFG->getPAGNode();
  return nullptr;
}

FunctionAnalysisData *AnalyzePass::getFunctionAnalysisData(Function &F) {
  auto it = functionAnalysisData.find(&F);
  if (it == functionAnalysisData.end())
    return nullptr;
  return &it->second;
}
