#include "AnalyzePass.h"

#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/User.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/SmallSet.h>

#include "SVF-FE/LLVMUtil.h"
#include "Graphs/SVFG.h"
#include "WPA/Andersen.h"
#include "Util/Options.h"
#include "SVF-FE/PAGBuilder.h"

using namespace llvm;
using namespace SVF;

char AnalyzePass::ID = 0;

bool AnalyzePass::doInitialization(Module &M)
{
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
    VFG *vfg = new VFG(callgraph);

    /// Sparse value-flow graph (SVFG)
    SVFGBuilder svfBuilder;
    SVFG *svfg = svfBuilder.buildFullSVFGWithoutOPT(ander);

    /// Collect uses of an LLVM Value
    /// traverseOnVFG(svfg, value);

    /// Collect all successor nodes on ICFG
    /// traverseOnICFG(icfg, value);

    // clean up memory
    delete vfg;
    delete svfg;
    AndersenWaveDiff::releaseAndersenWaveDiff();
    PAG::releasePAG();

    LLVMModuleSet::getLLVMModuleSet()->dumpModulesToFile(".svf.bc");

    return 0;
}

/*!
 * An example to query/collect all the uses of a definition of a value along value-flow graph (VFG)
 */
void traverseOnVFG(const SVFG *vfg, Value *val)
{
    PAG *pag = PAG::getPAG();

    PAGNode *pNode = pag->getPAGNode(pag->getValueNode(val));
    const VFGNode *vNode = vfg->getDefSVFGNode(pNode);
    FIFOWorkList<const VFGNode *> worklist;
    Set<const VFGNode *> visited;
    worklist.push(vNode);

    /// Traverse along VFG
    while (!worklist.empty())
    {
        const VFGNode *vNode = worklist.pop();
        for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                                                                     vNode->OutEdgeEnd();
             it != eit; ++it)
        {
            VFGEdge *edge = *it;
            VFGNode *succNode = edge->getDstNode();
            if (visited.find(succNode) == visited.end())
            {
                visited.insert(succNode);
                worklist.push(succNode);
            }
        }
    }

    /// Collect all LLVM Values
    for (Set<const VFGNode *>::const_iterator it = visited.begin(), eit = visited.end(); it != eit; ++it)
    {
        const VFGNode *node = *it;
        /// can only query VFGNode involving top-level pointers (starting with % or @ in LLVM IR)
        /// PAGNode* pNode = vfg->getLHSTopLevPtr(node);
        /// Value* val = pNode->getValue();
    }
}

bool AnalyzePass::runOnFunction(Function &F)
{
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

    ValueMap<Value *, llvm::SmallVector<Value *, 0> *> VMap;

    for (BasicBlock &B : F)
    {
        SmallSet<Value *, 8> BasicBlockDeps;
        errs() << B.getName() << "\n";
        for (Instruction &I : B)
        {

            llvm::SmallVector<Value *, 0> operands;
            for (Use &U : I.operands())
            {
                if (dyn_cast<BasicBlock>(U.get()))
                {
                    continue;
                }
                operands.push_back(U.get());
                BasicBlockDeps.insert(U.get());
            }
            VMap.insert(std::make_pair(&I, &operands));
        }

        for (Value *Dep : BasicBlockDeps)
        {
            errs() << *Dep << "\n";
        }
        // errs() << "getting BasicBlock" << B << "\n";
    }

    errs() << "EndOfFunction\n\n";
    return false;
}

llvm::ValueMap<llvm::BasicBlock *, std::string *> *AnalyzePass::getFunctionAnalysisData(Function &F)
{
    return functionAnalysisData.lookup(&F);
}
