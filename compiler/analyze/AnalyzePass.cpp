#include "AnalyzePass.h"

#include <llvm/ADT/SmallSet.h>
#include <llvm/ADT/SmallVector.h>
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

  /// Query aliases
  /// aliasQuery(ander,value1,value2);

  /// Print points-to information
  /// printPts(ander, value1);

  /// Call Graph
  PTACallGraph *callgraph = ander->getPTACallGraph();

  /// ICFG
  ICFG *icfg = pag->getICFG();

  /// Value-Flow Graph (VFG)
  vfg = new VFG(callgraph);

  /// Sparse value-flow graph (SVFG)
  SVFGBuilder svfBuilder;
  svfg = svfBuilder.buildFullSVFGWithoutOPT(ander);

  /// Collect uses of an LLVM Value
  /// traverseOnVFG(svfg, value);

  /// Collect all successor nodes on ICFG
  /// traverseOnICFG(icfg, value);

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

/*!
 * An example to query/collect all the uses of a definition of a value along
 * value-flow graph (VFG)
 */
void traverseOnVFG(const SVFG *vfg, Value *val) {
  PAG *pag = PAG::getPAG();

  PAGNode *pNode = pag->getPAGNode(pag->getValueNode(val));
  const VFGNode *vNode = vfg->getDefSVFGNode(pNode);
  FIFOWorkList<const VFGNode *> worklist;
  Set<const VFGNode *> visited;
  worklist.push(vNode);

  /// Traverse along VFG
  while (!worklist.empty()) {
    const VFGNode *vNode = worklist.pop();
    for (VFGNode::const_iterator it = vNode->OutEdgeBegin(),
                                 eit = vNode->OutEdgeEnd();
         it != eit; ++it) {
      VFGEdge *edge = *it;
      VFGNode *succNode = edge->getDstNode();
      if (visited.find(succNode) == visited.end()) {
        visited.insert(succNode);
        worklist.push(succNode);
      }
    }
  }

  /// Collect all LLVM Values
  for (Set<const VFGNode *>::const_iterator it = visited.begin(),
                                            eit = visited.end();
       it != eit; ++it) {
    const VFGNode *node = *it;
    /// can only query VFGNode involving top-level pointers (starting with % or
    /// @ in LLVM IR) PAGNode* pNode = vfg->getLHSTopLevPtr(node); Value* val =
    /// pNode->getValue();
  }
}

bool AnalyzePass::runOnFunction(Function &F) {
  if (F.getName() != "a") {
    return false;
  }
  errs() << "getting function: " << F.getName() << "\n";
  /*for (Argument &A : F.args())
  {
      if (A.user_empty())
      {
          continue;
      }
      errs() << "getting arg" << A << "\n";
      for (User *U : A.users())
      {
          if (auto I = dyn_cast<Instruction>(U))
          {
              errs() << "  Inst:" << *I << "\n";
          }
          else
          {
              errs() << " User:" << U->getName() << "\n";
          }
      }
  }*/

  for (BasicBlock &B : F)

  /**
   * @brief For each basic block I want to get the most simplified and
   * summarized values that need to be concreteness-checked. This means on each
   * used operand for instructions such as add, div, mul needs to be checked
   * with the value-flow tree But as we want to check it for this basic block,
   * we basically need to find the first dependency that is defined in the same
   * function outside the basic block or still inside said basic block?
   */
  {
    ValueMap<Value *, llvm::SmallVector<Value *, 0> *> VMap;
    SmallSet<Value *, 8> BasicBlockDeps;
    errs() << B.getName() << "\n";
    for (Instruction &I : B) {

      llvm::SmallVector<Value *, 0> operands;
      for (Use &U : I.operands()) {
        if (dyn_cast<BasicBlock>(U.get())) {
          continue;
        }
        operands.push_back(U.get());
        BasicBlockDeps.insert(U.get()); // collect all operands
      }
      VMap.insert(std::make_pair(&I, &operands));
    }

    for (Value *Dep : BasicBlockDeps) {
      traversePredecessors(B, Dep);
      // errs() << *Dep << "\n";
    }
    // errs() << "getting BasicBlock" << B << "\n";
  }

  errs() << "EndOfFunction\n\n";
  return false;
}

const SVF::PAGNode *getLHSTopLevPtr(const VFGNode *);

llvm::Value *AnalyzePass::traversePredecessors(llvm::BasicBlock &BB,
                                               llvm::Value *Value) {

  SVF::PAG *pag = PAG::getPAG();

  SVF::PAGNode *pNode = pag->getPAGNode(pag->getValueNode(Value));
  const VFGNode *vNode = svfg->getDefSVFGNode(pNode);

  errs() << "Value: " << *Value << "\n";
  for (auto *edge : vNode->getInEdges()) {
    const VFGNode *node = edge->getSrcNode();
    auto *someNode = getLHSTopLevPtr(node);
    if (someNode == nullptr) {
      continue;
    }
    const llvm::Value *val = someNode->getValue();
    errs() << "Edge: " << *edge->getSrcNode() << "\n";
    errs() << "In Value: " << *val << "\n";
  }
  errs() << "\n";

  return Value;
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

llvm::ValueMap<llvm::BasicBlock *, std::string *> *
AnalyzePass::getFunctionAnalysisData(Function &F) {
  return functionAnalysisData.lookup(&F);
}
