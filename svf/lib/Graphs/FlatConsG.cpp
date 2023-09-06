
#include "Graphs/FlatConsG.h"
#include "Util/Options.h"

using namespace SVF;
using namespace SVFUtil;


/*!
 * Start building constraint graph
 */
void FConstraintGraph::buildFCG()
{

    // initialize nodes
    for(SVFIR::iterator it = pag->begin(), eit = pag->end(); it!=eit; ++it)
    {
        addFConstraintNode(new FConstraintNode(it->first), it->first);
    }

    // initialize edges
    SVFStmt::SVFStmtSetTy& addrs = getPAGEdgeSet(SVFStmt::Addr);
    for (SVFStmt::SVFStmtSetTy::iterator iter = addrs.begin(), eiter =
                addrs.end(); iter != eiter; ++iter)
    {
        const AddrStmt* edge = SVFUtil::cast<AddrStmt>(*iter);
        addAddrFCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& copys = getPAGEdgeSet(SVFStmt::Copy);
    for (SVFStmt::SVFStmtSetTy::iterator iter = copys.begin(), eiter =
                copys.end(); iter != eiter; ++iter)
    {
        const CopyStmt* edge = SVFUtil::cast<CopyStmt>(*iter);
        addCopyFCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& phis = getPAGEdgeSet(SVFStmt::Phi);
    for (SVFStmt::SVFStmtSetTy::iterator iter = phis.begin(), eiter =
                phis.end(); iter != eiter; ++iter)
    {
        const PhiStmt* edge = SVFUtil::cast<PhiStmt>(*iter);
        for(const auto opVar : edge->getOpndVars())
            addCopyFCGEdge(opVar->getId(),edge->getResID());
    }

    SVFStmt::SVFStmtSetTy& selects = getPAGEdgeSet(SVFStmt::Select);
    for (SVFStmt::SVFStmtSetTy::iterator iter = selects.begin(), eiter =
                selects.end(); iter != eiter; ++iter)
    {
        const SelectStmt* edge = SVFUtil::cast<SelectStmt>(*iter);
        for(const auto opVar : edge->getOpndVars())
            addCopyFCGEdge(opVar->getId(),edge->getResID());
    }

    SVFStmt::SVFStmtSetTy& calls = getPAGEdgeSet(SVFStmt::Call);
    for (SVFStmt::SVFStmtSetTy::iterator iter = calls.begin(), eiter =
                calls.end(); iter != eiter; ++iter)
    {
        const CallPE* edge = SVFUtil::cast<CallPE>(*iter);
        addCopyFCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& rets = getPAGEdgeSet(SVFStmt::Ret);
    for (SVFStmt::SVFStmtSetTy::iterator iter = rets.begin(), eiter =
                rets.end(); iter != eiter; ++iter)
    {
        const RetPE* edge = SVFUtil::cast<RetPE>(*iter);
        addCopyFCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& tdfks = getPAGEdgeSet(SVFStmt::ThreadFork);
    for (SVFStmt::SVFStmtSetTy::iterator iter = tdfks.begin(), eiter =
                tdfks.end(); iter != eiter; ++iter)
    {
        const TDForkPE* edge = SVFUtil::cast<TDForkPE>(*iter);
        addCopyFCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& tdjns = getPAGEdgeSet(SVFStmt::ThreadJoin);
    for (SVFStmt::SVFStmtSetTy::iterator iter = tdjns.begin(), eiter =
                tdjns.end(); iter != eiter; ++iter)
    {
        const TDJoinPE* edge = SVFUtil::cast<TDJoinPE>(*iter);
        addCopyFCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& ngeps = getPAGEdgeSet(SVFStmt::Gep);
    for (SVFStmt::SVFStmtSetTy::iterator iter = ngeps.begin(), eiter =
                ngeps.end(); iter != eiter; ++iter)
    {
        GepStmt* edge = SVFUtil::cast<GepStmt>(*iter);
        if(edge->isVariantFieldGep())
            addVariantGepFCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
        else
            addNormalGepFCGEdge(edge->getRHSVarID(),edge->getLHSVarID(),edge->getAccessPath());
    }

    SVFStmt::SVFStmtSetTy& loads = getPAGEdgeSet(SVFStmt::Load);
    for (SVFStmt::SVFStmtSetTy::iterator iter = loads.begin(), eiter =
                loads.end(); iter != eiter; ++iter)
    {
        LoadStmt* edge = SVFUtil::cast<LoadStmt>(*iter);
        addLoadFCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& stores = getPAGEdgeSet(SVFStmt::Store);
    for (SVFStmt::SVFStmtSetTy::iterator iter = stores.begin(), eiter =
                stores.end(); iter != eiter; ++iter)
    {
        StoreStmt* edge = SVFUtil::cast<StoreStmt>(*iter);
        addStoreFCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }
}


/*!
 * Memory has been cleaned up at GenericGraph
 */
void FConstraintGraph::destroy()
{
}

/*!
 * Constructor for address constraint graph edge
 */
AddrFCGEdge::AddrFCGEdge(FConstraintNode* s, FConstraintNode* d, EdgeID id)
    : FConstraintEdge(s,d,FAddr,id)
{
    // Retarget addr edges may lead s to be a dummy node
    PAGNode* node = SVFIR::getPAG()->getGNode(s->getId());
    (void)node; // Suppress warning of unused variable under release build
    if (!SVFModule::pagReadFromTXT())
    {
        assert(!SVFUtil::isa<DummyValVar>(node) && "a dummy node??");
    }
}

/*!
 * Add an address edge
 */
AddrFCGEdge* FConstraintGraph::addAddrFCGEdge(NodeID src, NodeID dst)
{
    FConstraintNode* srcNode = getFConstraintNode(src);
    FConstraintNode* dstNode = getFConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, FConstraintEdge::FAddr)) /// TODO: multi edge
        return nullptr;
    AddrFCGEdge* edge = new AddrFCGEdge(srcNode, dstNode, edgeIndex++);

    bool inserted = AddrFCGEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new AddrFCGEdge not added??");

    srcNode->addOutgoingAddrEdge(edge);
    dstNode->addIncomingAddrEdge(edge);
    return edge;
}

/*!
 * Add Copy edge
 */
CopyFCGEdge* FConstraintGraph::addCopyFCGEdge(NodeID src, NodeID dst, FConstraintEdge* complexEdge)
{
    FConstraintNode* srcNode = getFConstraintNode(src);
    FConstraintNode* dstNode = getFConstraintNode(dst);
    if (srcNode == dstNode)
        return nullptr;
    if (complexEdge == nullptr) {
        // Copy added via buildFCG
        if (hasEdge(srcNode, dstNode, FConstraintEdge::FCopy))
            return nullptr;
        
        CopyFCGEdge* edge = new CopyFCGEdge(srcNode, dstNode, edgeIndex++);
        edge->addComplexEdge(edge);
        bool inserted = directFEdgeSet.insert(edge).second;
        (void)inserted; // Suppress warning of unused variable under release build
        assert(inserted && "new CopyFCGEdge not added??");

        srcNode->addOutgoingCopyEdge(edge);
        dstNode->addIncomingCopyEdge(edge);
        return edge;
    }
    else {
        // Copy added via complex constraint

        if (hasEdge(srcNode, dstNode, FConstraintEdge::FCopy)) {
            FConstraintEdge* oldEdge = getEdge(srcNode, dstNode, FConstraintEdge::FCopy);
            CopyFCGEdge* oldCopy = SVFUtil::dyn_cast<CopyFCGEdge>(oldEdge);
            // bool add = oldCopy->addComplexEdge(complexEdge);
            oldCopy->addComplexEdge(complexEdge);
            return nullptr;
        } 

        CopyFCGEdge* edge = new CopyFCGEdge(srcNode, dstNode, edgeIndex++);
        edge->addComplexEdge(complexEdge);
        bool inserted = directFEdgeSet.insert(edge).second;
        (void)inserted; // Suppress warning of unused variable under release build
        assert(inserted && "new CopyFCGEdge not added??");

        srcNode->addOutgoingCopyEdge(edge);
        dstNode->addIncomingCopyEdge(edge);
        return edge;
    }
}


/*!
 * Add Gep edge
 */
NormalGepFCGEdge*  FConstraintGraph::addNormalGepFCGEdge(NodeID src, NodeID dst, const AccessPath& ap)
{
    FConstraintNode* srcNode = getFConstraintNode(src);
    FConstraintNode* dstNode = getFConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, FConstraintEdge::FNormalGep)) /// TODO: multi edge
        return nullptr;

    NormalGepFCGEdge* edge =
        new NormalGepFCGEdge(srcNode, dstNode, ap, edgeIndex++);

    bool inserted = directFEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new NormalGepFCGEdge not added??");

    srcNode->addOutgoingGepEdge(edge);
    dstNode->addIncomingGepEdge(edge);
    return edge;
}


/*!
 * Add variant gep edge
 */
VariantGepFCGEdge* FConstraintGraph::addVariantGepFCGEdge(NodeID src, NodeID dst)
{
    FConstraintNode* srcNode = getFConstraintNode(src);
    FConstraintNode* dstNode = getFConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, FConstraintEdge::FVariantGep))
        return nullptr;

    VariantGepFCGEdge* edge = new VariantGepFCGEdge(srcNode, dstNode, edgeIndex++);

    bool inserted = directFEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new VariantGepFCGEdge not added??");

    srcNode->addOutgoingGepEdge(edge);
    dstNode->addIncomingGepEdge(edge);
    return edge;
}

/*!
 * Add Load edge
 */
LoadFCGEdge* FConstraintGraph::addLoadFCGEdge(NodeID src, NodeID dst)
{
    FConstraintNode* srcNode = getFConstraintNode(src);
    FConstraintNode* dstNode = getFConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, FConstraintEdge::FLoad)) /// TODO: multi edge
        return nullptr;

    LoadFCGEdge* edge = new LoadFCGEdge(srcNode, dstNode, edgeIndex++);

    bool inserted = LoadFCGEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new LoadFCGEdge not added??");

    srcNode->addOutgoingLoadEdge(edge);
    dstNode->addIncomingLoadEdge(edge);
    return edge;
}

/*!
 * Add Store edge
 */
StoreFCGEdge* FConstraintGraph::addStoreFCGEdge(NodeID src, NodeID dst)
{
    FConstraintNode* srcNode = getFConstraintNode(src);
    FConstraintNode* dstNode = getFConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, FConstraintEdge::FStore)) /// TODO: multi edge
        return nullptr;

    StoreFCGEdge* edge = new StoreFCGEdge(srcNode, dstNode, edgeIndex++);

    bool inserted = StoreFCGEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new StoreFCGEdge not added??");

    srcNode->addOutgoingStoreEdge(edge);
    dstNode->addIncomingStoreEdge(edge);
    return edge;
}

/*!
 * Remove addr edge from their src and dst edge sets
 */
void FConstraintGraph::removeAddrEdge(AddrFCGEdge* edge)
{
    getFConstraintNode(edge->getSrcID())->removeOutgoingAddrEdge(edge);
    getFConstraintNode(edge->getDstID())->removeIncomingAddrEdge(edge);
    u32_t num = AddrFCGEdgeSet.erase(edge);
    (void)num; // Suppress warning of unused variable under release build
    assert(num && "edge not in the set, can not remove!!!");
    delete edge;
}

/*!
 * Remove load edge from their src and dst edge sets
 */
void FConstraintGraph::removeLoadEdge(LoadFCGEdge* edge)
{
    getFConstraintNode(edge->getSrcID())->removeOutgoingLoadEdge(edge);
    getFConstraintNode(edge->getDstID())->removeIncomingLoadEdge(edge);
    u32_t num = LoadFCGEdgeSet.erase(edge);
    (void)num; // Suppress warning of unused variable under release build
    assert(num && "edge not in the set, can not remove!!!");
    delete edge;
}

/*!
 * Remove store edge from their src and dst edge sets
 */
void FConstraintGraph::removeStoreEdge(StoreFCGEdge* edge)
{
    getFConstraintNode(edge->getSrcID())->removeOutgoingStoreEdge(edge);
    getFConstraintNode(edge->getDstID())->removeIncomingStoreEdge(edge);
    u32_t num = StoreFCGEdgeSet.erase(edge);
    (void)num; // Suppress warning of unused variable under release build
    assert(num && "edge not in the set, can not remove!!!");
    delete edge;
}

/*!
 * Remove edges from their src and dst edge sets
 */
void FConstraintGraph::removeDirectEdge(FConstraintEdge* edge)
{

    getFConstraintNode(edge->getSrcID())->removeOutgoingDirectEdge(edge);
    getFConstraintNode(edge->getDstID())->removeIncomingDirectEdge(edge);
    u32_t num = directFEdgeSet.erase(edge);
    (void)num; // Suppress warning of unused variable under release build
    assert(num && "edge not in the set, can not remove!!!");
    delete edge;
}

CopyFCGEdge* FConstraintGraph::removeCopyFCGEdgeByComplex(NodeID src, NodeID dst, 
    FConstraintEdge* complexEdge)
{
    FConstraintNode* srcNode = getFConstraintNode(src);
    FConstraintNode* dstNode = getFConstraintNode(dst);
    if (srcNode == dstNode)
        return nullptr;
    if (!hasEdge(srcNode, dstNode, FConstraintEdge::FCopy))
        return nullptr;
    FConstraintEdge* edge = getEdge(srcNode, dstNode, FConstraintEdge::FCopy);
    CopyFCGEdge* copy = SVFUtil::dyn_cast<CopyFCGEdge>(edge);
    if (complexEdge == nullptr) {
        // Copy removed without complex constraint
        copy->removeComplexEdge(edge);
    }
    else {
        // Copy removed by complex constraint
        copy->removeComplexEdge(complexEdge);
    }
    if (copy->getComplexEdgeSet().size() == 0)
    {
        // Copy should be removed from constraint graph
        removeDirectEdge(edge);
        return nullptr;
    }
    return copy;
}

/*!
 * Dump constraint graph
 */
void FConstraintGraph::dump(std::string name)
{
    GraphPrinter::WriteGraphToFile(outs(), name, this);
}

/*!
 * Print this constraint graph including its nodes and edges
 */
void FConstraintGraph::print()
{

    outs() << "-----------------FConstraintGraph--------------------------------------\n";

    FConstraintEdge::FConstraintEdgeSetTy& addrs = this->getAddrFCGEdges();
    for (FConstraintEdge::FConstraintEdgeSetTy::iterator iter = addrs.begin(),
            eiter = addrs.end(); iter != eiter; ++iter)
    {
        outs() << (*iter)->getSrcID() << " -- FAddr --> " << (*iter)->getDstID()
               << "\n";
    }

    FConstraintEdge::FConstraintEdgeSetTy& directs = this->getDirectFCGEdges();
    for (FConstraintEdge::FConstraintEdgeSetTy::iterator iter = directs.begin(),
            eiter = directs.end(); iter != eiter; ++iter)
    {
        if (CopyFCGEdge* copy = SVFUtil::dyn_cast<CopyFCGEdge>(*iter))
        {
            outs() << copy->getSrcID() << " -- FCopy --> " << copy->getDstID()
                   << "\n";
        }
        else if (NormalGepFCGEdge* ngep = SVFUtil::dyn_cast<NormalGepFCGEdge>(*iter))
        {
            outs() << ngep->getSrcID() << " -- FNormalGep (" << ngep->getConstantFieldIdx()
                   << ") --> " << ngep->getDstID() << "\n";
        }
        else if (VariantGepFCGEdge* vgep = SVFUtil::dyn_cast<VariantGepFCGEdge>(*iter))
        {
            outs() << vgep->getSrcID() << " -- FVarintGep --> "
                   << vgep->getDstID() << "\n";
        }
        else
            assert(false && "wrong flat constraint edge kind!");
    }

    FConstraintEdge::FConstraintEdgeSetTy& loads = this->getLoadFCGEdges();
    for (FConstraintEdge::FConstraintEdgeSetTy::iterator iter = loads.begin(),
            eiter = loads.end(); iter != eiter; ++iter)
    {
        outs() << (*iter)->getSrcID() << " -- FLoad --> " << (*iter)->getDstID()
               << "\n";
    }

    FConstraintEdge::FConstraintEdgeSetTy& stores = this->getStoreFCGEdges();
    for (FConstraintEdge::FConstraintEdgeSetTy::iterator iter = stores.begin(),
            eiter = stores.end(); iter != eiter; ++iter)
    {
        outs() << (*iter)->getSrcID() << " -- FStore --> " << (*iter)->getDstID()
               << "\n";
    }

    outs()
            << "--------------------------------------------------------------\n";

}

/*!
 * View dot graph of Constraint graph from debugger.
 */
void FConstraintGraph::view()
{
    SVF::ViewGraph(this, "Flat Constraint Graph");
}

/// Iterators of direct edges for ConsGNode
//@{
FConstraintNode::iterator FConstraintNode::directOutEdgeBegin()
{
    if (Options::DetectPWC())
        return directOutEdges.begin();
    else
        return copyOutEdges.begin();
}

FConstraintNode::iterator FConstraintNode::directOutEdgeEnd()
{
    if (Options::DetectPWC())
        return directOutEdges.end();
    else
        return copyOutEdges.end();
}

FConstraintNode::iterator FConstraintNode::directInEdgeBegin()
{
    if (Options::DetectPWC())
        return directInEdges.begin();
    else
        return copyInEdges.begin();
}

FConstraintNode::iterator FConstraintNode::directInEdgeEnd()
{
    if (Options::DetectPWC())
        return directInEdges.end();
    else
        return copyInEdges.end();
}

FConstraintNode::const_iterator FConstraintNode::directOutEdgeBegin() const
{
    if (Options::DetectPWC())
        return directOutEdges.begin();
    else
        return copyOutEdges.begin();
}

FConstraintNode::const_iterator FConstraintNode::directOutEdgeEnd() const
{
    if (Options::DetectPWC())
        return directOutEdges.end();
    else
        return copyOutEdges.end();
}

FConstraintNode::const_iterator FConstraintNode::directInEdgeBegin() const
{
    if (Options::DetectPWC())
        return directInEdges.begin();
    else
        return copyInEdges.begin();
}

FConstraintNode::const_iterator FConstraintNode::directInEdgeEnd() const
{
    if (Options::DetectPWC())
        return directInEdges.end();
    else
        return copyInEdges.end();
}
//@}

/*!
 * GraphTraits specialization for flat constraint graph
 */
namespace SVF
{
template<>
struct DOTGraphTraits<FConstraintGraph*> : public DOTGraphTraits<SVFIR*>
{

    typedef FConstraintNode NodeType;
    DOTGraphTraits(bool isSimple = false) :
        DOTGraphTraits<SVFIR*>(isSimple)
    {
    }

    /// Return name of the graph
    static std::string getGraphName(FConstraintGraph*)
    {
        return "FConstraintG";
    }

    static bool isNodeHidden(NodeType *n, FConstraintGraph *)
    {
        if (Options::ShowHiddenNode()) return false;
        else return (n->getInEdges().empty() && n->getOutEdges().empty());
    }

    /// Return label of a VFG node with two display mode
    /// Either you can choose to display the name of the value or the whole instruction
    static std::string getNodeLabel(NodeType *n, FConstraintGraph*)
    {
        PAGNode* node = SVFIR::getPAG()->getGNode(n->getId());
        bool briefDisplay = Options::BriefConsCGDotGraph();
        bool nameDisplay = true;
        std::string str;
        std::stringstream rawstr(str);

        if (briefDisplay)
        {
            if (SVFUtil::isa<ValVar>(node))
            {
                if (nameDisplay)
                    rawstr << node->getId() << ":" << node->getValueName();
                else
                    rawstr << node->getId();
            }
            else
                rawstr << node->getId();
        }
        else
        {
            // print the whole value
            if (!SVFUtil::isa<DummyValVar>(node) && !SVFUtil::isa<DummyObjVar>(node))
                rawstr << node->getId() << ":" << node->getValue()->toString();
            else
                rawstr << node->getId() << ":";

        }

        return rawstr.str();
    }

    static std::string getNodeAttributes(NodeType *n, FConstraintGraph*)
    {
        PAGNode* node = SVFIR::getPAG()->getGNode(n->getId());
        if (SVFUtil::isa<ValVar>(node))
        {
            if(SVFUtil::isa<GepValVar>(node))
                return "shape=hexagon";
            else if (SVFUtil::isa<DummyValVar>(node))
                return "shape=diamond";
            else
                return "shape=box";
        }
        else if (SVFUtil::isa<ObjVar>(node))
        {
            if(SVFUtil::isa<GepObjVar>(node))
                return "shape=doubleoctagon";
            else if(SVFUtil::isa<FIObjVar>(node))
                return "shape=box3d";
            else if (SVFUtil::isa<DummyObjVar>(node))
                return "shape=tab";
            else
                return "shape=component";
        }
        else if (SVFUtil::isa<RetPN>(node))
        {
            return "shape=Mrecord";
        }
        else if (SVFUtil::isa<VarArgPN>(node))
        {
            return "shape=octagon";
        }
        else
        {
            assert(0 && "no such kind!!");
        }
        return "";
    }

    template<class EdgeIter>
    static std::string getEdgeAttributes(NodeType*, EdgeIter EI, FConstraintGraph*)
    {
        FConstraintEdge* edge = *(EI.getCurrent());
        assert(edge && "No edge found!!");
        if (edge->getEdgeKind() == FConstraintEdge::FAddr)
        {
            return "color=green";
        }
        else if (edge->getEdgeKind() == FConstraintEdge::FCopy)
        {
            return "color=black";
        }
        else if (edge->getEdgeKind() == FConstraintEdge::FNormalGep
                 || edge->getEdgeKind() == FConstraintEdge::FVariantGep)
        {
            return "color=purple";
        }
        else if (edge->getEdgeKind() == FConstraintEdge::FStore)
        {
            return "color=blue";
        }
        else if (edge->getEdgeKind() == FConstraintEdge::FLoad)
        {
            return "color=red";
        }
        else
        {
            assert(0 && "No such kind edge!!");
        }
        return "";
    }

    template<class EdgeIter>
    static std::string getEdgeSourceLabel(NodeType*, EdgeIter)
    {
        return "";
    }
};
} // End namespace llvm
