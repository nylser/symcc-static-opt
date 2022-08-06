#include "AnalyzePass.h"

#include "../split/SplitPass.h"
#include <llvm/IR/Argument.h>
#include <llvm/IR/User.h>
#include <llvm/Support/raw_ostream.h>

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Woverloaded-virtual"
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-variable"
#pragma clang diagnostic ignored "-Wself-assign"
#pragma clang diagnostic ignored "-Wignored-qualifiers"
#include "SVF-FE/LLVMUtil.h"
#include "SVF-FE/PAGBuilder.h"
#include "Util/Options.h"
#include "Util/SVFModule.h"
#include "WPA/Andersen.h"
#pragma clang diagnostic pop

using namespace llvm;
using namespace SVF;

char AnalyzePass::ID = 0;

bool AnalyzePass::runOnModule(Module &M) {
  // errs() << "initializing analyze pass: " << M.getName() << "\n";
  SVFModule *svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(M);
  svfModule->buildSymbolTableInfo();

  /// Build Program Assignment Graph (PAG)
  PAGBuilder builder;
  PAG *pag = builder.build(svfModule);

  /// Create Andersen's pointer analysis
  Andersen *ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

  /// Call Graph
  PTACallGraph *callgraph = ander->getPTACallGraph();

  /// Value-Flow Graph (VFG)
  vfg = new VFG(callgraph);

  /// Sparse value-flow graph (SVFG)
  SVFGBuilder svfBuilder;
  svfg = svfBuilder.buildFullSVFGWithoutOPT(ander);
  for (Function &F : M.functions()) {
    if (F.size() == 0) {
      // errs() << "skipping empty function: " << F.getName() << "\n";
      continue;
    }
    // errs() << "getting function: " << F.getName() << "\n";
    LoopInfo &loopInfo = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
    FunctionAnalysisData *data = &functionAnalysisData[&F];
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
      auto loop = loopInfo.getLoopFor(&B);
      if (loop != nullptr) {
        // errs() << B.getName() << " loop: " << *loop << "\n";
      }
      SmallSet<Value *, 8> basicBlockDeps;

      std::set<const Value *> *topLevelDepsList = &data->basicBlockData[&B];

      for (Instruction &I : B) {

        if (auto *loadInst = dyn_cast<LoadInst>(&I)) {
          // load instructions are split in Symbolizer
          auto nextInst = loadInst->getNextNode();
          auto brInst = dyn_cast<BranchInst>(nextInst);
          // check that load splitting actually occured.
          assert(brInst != nullptr && brInst->isUnconditional() &&
                 "after each load instruction, there should be an "
                 "unconditional branch instruction (load splitting)");

          // add this load instruction to the concreteness dependencies for the
          // next block, so that we can perform the concreteness check after
          // load splitting
          data->basicBlockData[brInst->getSuccessor(0)].insert(loadInst);
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
      }

      for (auto *topLevelDep : basicBlockTopLevelDeps) {
        topLevelDepsList->insert(topLevelDep);
        // errs() << "Dep: " << *topLevelDep << "\n";
      }
    }
  }

  // clean up memory
  delete vfg;
  delete svfg;
  AndersenWaveDiff::releaseAndersenWaveDiff();
  PAG::releasePAG();

  return false;
}

const SVF::PAGNode *getLHSTopLevPtr(const VFGNode *);

llvm::SmallSet<const llvm::Value *, 8>
AnalyzePass::traversePredecessors(llvm::BasicBlock &BB, llvm::Value *Value) {
  // errs() << *Value << "\n";
  auto it = valueDependencies.find(Value);
  if (it != valueDependencies.end()) {
    // errs() << "short circuit!\n";
    return it->second;
  }
  llvm::SmallSet<const llvm::Value *, 8> topLevel;
  SVF::PAG *pag = PAG::getPAG();
  SVF::FIFOWorkList<const VFGNode *> worklist;
  if (dyn_cast<Constant>(Value)) {
    return topLevel;
  }
  // errs() << "Processing " << *Value << "\n";
  SVF::PAGNode *pNode = pag->getPAGNode(pag->getValueNode(Value));
  const VFGNode *vNode = svfg->getDefSVFGNode(pNode);
  worklist.push(vNode);

  std::set<const VFGNode *> visited;

  while (!worklist.empty()) {
    auto *currentNode = worklist.pop();
    if (visited.find(currentNode) != visited.end()) {
      /** Skip already visited nodes**/
      // errs() << "Analysis: Skipping already visited node: " << *currentNode
      //        << "\n";
      // errs() << "Anaylsis: While analysing: " << *Value << "\n";
      continue;
    }
    visited.insert(currentNode);
    auto *pagNode = getLHSTopLevPtr(currentNode);

    if (pagNode != nullptr) {
      if (pagNode->getNodeKind() == pagNode->DummyObjNode ||
          pagNode->getNodeKind() == pagNode->DummyValNode) {
        // errs() << "Skipping DummyNode! " << *currentNode << "\n";
        continue;
      }
      const llvm::Value *nodeValue = pagNode->getValue();
      if (auto *param = dyn_cast<llvm::Argument>(nodeValue)) {
        topLevel.insert(param);
        continue;
      }
      if (auto *inst = dyn_cast<llvm::Instruction>(nodeValue)) {
        if (auto *alloca = dyn_cast<llvm::AllocaInst>(inst)) {
          // skip alloca instructions => pointers are always concrete
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

void AnalyzePass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesCFG();
  AU.addRequired<SplitPass>();
  AU.addRequired<LoopInfoWrapperPass>();
}

FunctionAnalysisData *AnalyzePass::getFunctionAnalysisData(Function &F) {
  auto it = functionAnalysisData.find(&F);
  if (it == functionAnalysisData.end())
    return nullptr;
  return &it->second;
}
