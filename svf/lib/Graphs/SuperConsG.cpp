
#include "Graphs/FlatConsG.h"
#include "Graphs/SuperConsG.h"
#include "Util/Options.h"


using namespace SVF;
using namespace SVFUtil;

/*!
 * Start building super constraint graph
 */
void SConstraintGraph::buildSCG()
{

    // initialize nodes
    for(SVFIR::iterator it = pag->begin(), eit = pag->end(); it!=eit; ++it)
    {
        addSConstraintNode(new SConstraintNode(it->first), it->first);
    }

    // initialize edges
    SVFStmt::SVFStmtSetTy& addrs = getPAGEdgeSet(SVFStmt::Addr);
    for (SVFStmt::SVFStmtSetTy::iterator iter = addrs.begin(), eiter =
                addrs.end(); iter != eiter; ++iter)
    {
        const AddrStmt* edge = SVFUtil::cast<AddrStmt>(*iter);
        addAddrSCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& copys = getPAGEdgeSet(SVFStmt::Copy);
    for (SVFStmt::SVFStmtSetTy::iterator iter = copys.begin(), eiter =
                copys.end(); iter != eiter; ++iter)
    {
        const CopyStmt* edge = SVFUtil::cast<CopyStmt>(*iter);
        addCopySCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& phis = getPAGEdgeSet(SVFStmt::Phi);
    for (SVFStmt::SVFStmtSetTy::iterator iter = phis.begin(), eiter =
                phis.end(); iter != eiter; ++iter)
    {
        const PhiStmt* edge = SVFUtil::cast<PhiStmt>(*iter);
        for(const auto opVar : edge->getOpndVars())
            addCopySCGEdge(opVar->getId(),edge->getResID());
    }

    SVFStmt::SVFStmtSetTy& selects = getPAGEdgeSet(SVFStmt::Select);
    for (SVFStmt::SVFStmtSetTy::iterator iter = selects.begin(), eiter =
                selects.end(); iter != eiter; ++iter)
    {
        const SelectStmt* edge = SVFUtil::cast<SelectStmt>(*iter);
        for(const auto opVar : edge->getOpndVars())
            addCopySCGEdge(opVar->getId(),edge->getResID());
    }

    SVFStmt::SVFStmtSetTy& calls = getPAGEdgeSet(SVFStmt::Call);
    for (SVFStmt::SVFStmtSetTy::iterator iter = calls.begin(), eiter =
                calls.end(); iter != eiter; ++iter)
    {
        const CallPE* edge = SVFUtil::cast<CallPE>(*iter);
        addCopySCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& rets = getPAGEdgeSet(SVFStmt::Ret);
    for (SVFStmt::SVFStmtSetTy::iterator iter = rets.begin(), eiter =
                rets.end(); iter != eiter; ++iter)
    {
        const RetPE* edge = SVFUtil::cast<RetPE>(*iter);
        addCopySCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& tdfks = getPAGEdgeSet(SVFStmt::ThreadFork);
    for (SVFStmt::SVFStmtSetTy::iterator iter = tdfks.begin(), eiter =
                tdfks.end(); iter != eiter; ++iter)
    {
        const TDForkPE* edge = SVFUtil::cast<TDForkPE>(*iter);
        addCopySCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& tdjns = getPAGEdgeSet(SVFStmt::ThreadJoin);
    for (SVFStmt::SVFStmtSetTy::iterator iter = tdjns.begin(), eiter =
                tdjns.end(); iter != eiter; ++iter)
    {
        const TDJoinPE* edge = SVFUtil::cast<TDJoinPE>(*iter);
        addCopySCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& ngeps = getPAGEdgeSet(SVFStmt::Gep);
    for (SVFStmt::SVFStmtSetTy::iterator iter = ngeps.begin(), eiter =
                ngeps.end(); iter != eiter; ++iter)
    {
        GepStmt* edge = SVFUtil::cast<GepStmt>(*iter);
        if(edge->isVariantFieldGep())
            addVariantGepSCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
        else
            addNormalGepSCGEdge(edge->getRHSVarID(),edge->getLHSVarID(),edge->getAccessPath());
    }

    SVFStmt::SVFStmtSetTy& loads = getPAGEdgeSet(SVFStmt::Load);
    for (SVFStmt::SVFStmtSetTy::iterator iter = loads.begin(), eiter =
                loads.end(); iter != eiter; ++iter)
    {
        LoadStmt* edge = SVFUtil::cast<LoadStmt>(*iter);
        addLoadSCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }

    SVFStmt::SVFStmtSetTy& stores = getPAGEdgeSet(SVFStmt::Store);
    for (SVFStmt::SVFStmtSetTy::iterator iter = stores.begin(), eiter =
                stores.end(); iter != eiter; ++iter)
    {
        StoreStmt* edge = SVFUtil::cast<StoreStmt>(*iter);
        addStoreSCGEdge(edge->getRHSVarID(),edge->getLHSVarID());
    }
}

/*!
 * Memory has been cleaned up at GenericGraph
 */
void SConstraintGraph::destroy()
{
}

/*!
 * Constructor for address constraint graph edge
 */
AddrSCGEdge::AddrSCGEdge(SConstraintNode* s, SConstraintNode* d, EdgeID id)
    : SConstraintEdge(s,d,SAddr,id)
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
AddrSCGEdge* SConstraintGraph::addAddrSCGEdge(NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);
    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FAddr);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SAddr)) {
        // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SAddr);
        sEdge->addFEdge(fEdge);
        return nullptr;
    }
    AddrSCGEdge* edge = new AddrSCGEdge(srcNode, dstNode, edgeIndex++);
    edge->addFEdge(fEdge);
    bool inserted = AddrSCGEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new AddrCGEdge not added??");

    srcNode->addOutgoingAddrEdge(edge);
    dstNode->addIncomingAddrEdge(edge);
    return edge;
}

/*!
 * Remove an address edge
 */
AddrSCGEdge* SConstraintGraph::removeAddrSCGEdgeByFlat(NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);

    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FAddr);
    SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SAddr);

    AddrSCGEdge* sAddr = SVFUtil::dyn_cast<AddrSCGEdge>(sEdge);
    AddrFCGEdge* fAddr = SVFUtil::dyn_cast<AddrFCGEdge>(fEdge);
    sEdge->removeFEdge(fEdge);
    fConsG->removeAddrEdge(fAddr);
    if (sEdge->getFEdgeSet().size() == 0)
    {
        removeAddrEdge(sAddr);
        return nullptr;
    }
    return sAddr;
}

/*!
 * Add Copy edge
 */
CopySCGEdge* SConstraintGraph::addCopySCGEdge(NodeID src, NodeID dst, bool isRestore)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);
    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FCopy);
    if ((srcNode == dstNode) && (!isRestore))
        return nullptr;
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SCopy)) {
        // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SCopy);
        sEdge->addFEdge(fEdge);
        return nullptr;
    }

    CopySCGEdge* edge = new CopySCGEdge(srcNode, dstNode, edgeIndex++);
    edge->addFEdge(fEdge);
    bool inserted = directSEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new CopyCGEdge not added??");

    srcNode->addOutgoingCopyEdge(edge);
    dstNode->addIncomingCopyEdge(edge);
    return edge;
}

// /*!
//  * Remove a copy edge
//  */
// unsigned SConstraintGraph::removeCopySCGEdgeByFlat(NodeID src, NodeID dst) // TODO: --wjy
// {
//     SConstraintNode* srcNode = getSConstraintNode(src);
//     SConstraintNode* dstNode = getSConstraintNode(dst);
//     if (srcNode == dstNode)
//     {
//         // edgeInSCC todo
//         unsigned flag = sccBreakDetect(src, dst, FConstraintEdge::FCopy);
//         if (flag == 0) {
//             // SCC Restore: edge to be removed is still in fCG and sCG
//             // TODO: after redetect sub SCC, edge should be removed
//             return 1;
//         }
//         else if (flag == 1) {
//             // SCC Keep: edge has been removed from both fCG and sCG
//             return 0;
//         }
//     }
//     FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
//     FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);

//     FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FCopy);
//     SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SCopy);

//     // CopySCGEdge* copy = SVFUtil::dyn_cast<CopySCGEdge>(sEdge);
//     sEdge->removeFEdge(fEdge);
//     // fEdge-> 
//     if (sEdge->getFEdgeSet().size() == 0)
//     {
//         // TODO: scc detect
//         return 1;
//     }
//     // return copy;
//     return 0;
// }

/*!
 * Add Gep edge
 */
NormalGepSCGEdge* SConstraintGraph::addNormalGepSCGEdge(NodeID src, NodeID dst, const AccessPath& ap)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);
    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FNormalGep);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SNormalGep)) {
        // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SNormalGep);
        sEdge->addFEdge(fEdge);
        return nullptr;
    }

    NormalGepSCGEdge* edge =
        new NormalGepSCGEdge(srcNode, dstNode, ap, edgeIndex++);
    edge->addFEdge(fEdge);
    bool inserted = directSEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new NormalGepCGEdge not added??");

    srcNode->addOutgoingGepEdge(edge);
    dstNode->addIncomingGepEdge(edge);
    return edge;
}

/*!
 * Remove a ngep edge
 */
NormalGepSCGEdge* SConstraintGraph::removeNormalGepSCGEdgeByFlat(NodeID src, NodeID dst, const AccessPath& ap)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);
    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FNormalGep);
    if (!hasEdge(srcNode, dstNode, SConstraintEdge::SNormalGep)) {
        // add flat edge
        return nullptr;
    }
    SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SNormalGep);
    NormalGepSCGEdge* ngep = SVFUtil::dyn_cast<NormalGepSCGEdge>(sEdge);
    sEdge->removeFEdge(fEdge);
    if (sEdge->getFEdgeSet().size() == 0)
    {
        // TODO: scc detect
        
        return nullptr;
    }
    return ngep;
}

/*!
 * Add variant gep edge
 */
VariantGepSCGEdge* SConstraintGraph::addVariantGepSCGEdge(NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);
    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FVariantGep);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SVariantGep)) {
        // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SVariantGep);
        sEdge->addFEdge(fEdge);
        return nullptr;
    }

    VariantGepSCGEdge* edge = new VariantGepSCGEdge(srcNode, dstNode, edgeIndex++);
    edge->addFEdge(fEdge);
    bool inserted = directSEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new VariantGepCGEdge not added??");

    srcNode->addOutgoingGepEdge(edge);
    dstNode->addIncomingGepEdge(edge);
    return edge;
}

/*!
 * Remove a vgep edge
 */
VariantGepSCGEdge* SConstraintGraph::removeVariantGepSCGEdgeByFlat(NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);
    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FVariantGep);
    if (!hasEdge(srcNode, dstNode, SConstraintEdge::SVariantGep)) {
        // add flat edge
        return nullptr;
    }
    SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SVariantGep);
    VariantGepSCGEdge* vgep = SVFUtil::dyn_cast<VariantGepSCGEdge>(sEdge);
    sEdge->removeFEdge(fEdge);
    if (sEdge->getFEdgeSet().size() == 0)
    {
        // TODO: scc detect
        
        return nullptr;
    }
    return vgep;
}

/*!
 * Add Load edge
 */
LoadSCGEdge* SConstraintGraph::addLoadSCGEdge(NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);
    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FLoad);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SLoad)) {
        // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SLoad);
        sEdge->addFEdge(fEdge);
        return nullptr;
    }

    LoadSCGEdge* edge = new LoadSCGEdge(srcNode, dstNode, edgeIndex++);
    edge->addFEdge(fEdge);
    bool inserted = LoadSCGEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new LoadCGEdge not added??");

    srcNode->addOutgoingLoadEdge(edge);
    dstNode->addIncomingLoadEdge(edge);
    return edge;
}

/*!
 * Remove a Load edge
 */
LoadSCGEdge* SConstraintGraph::removeLoadSCGEdgeByFlat(NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);

    // if (!fConsG->hasEdge(fSrcNode, fDstNode, FConstraintEdge::FLoad)) {
    //     return nullptr;
    // }
    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FLoad);
    // if (!hasEdge(srcNode, dstNode, SConstraintEdge::SLoad)) {
    //     return nullptr;
    // }
    SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SLoad);

    LoadSCGEdge* sLoad = SVFUtil::dyn_cast<LoadSCGEdge>(sEdge);
    LoadFCGEdge* fLoad = SVFUtil::dyn_cast<LoadFCGEdge>(fEdge);
    sEdge->removeFEdge(fEdge); // remove fEdge from sEdge's fEdgeSet
    fConsG->removeLoadEdge(fLoad); // remove fEdge from fCG
    if (sEdge->getFEdgeSet().size() == 0)
    {   // if sEdge's fEdgeSet is empty, remove sEdge from sCG
        removeLoadEdge(sLoad);
        return nullptr;
    }
    return sLoad;
}

/*!
 * Add Store edge
 */
StoreSCGEdge* SConstraintGraph::addStoreSCGEdge(NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);
    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FStore);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SStore)) {
         // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SStore);
        sEdge->addFEdge(fEdge);
        return nullptr;
    }

    StoreSCGEdge* edge = new StoreSCGEdge(srcNode, dstNode, edgeIndex++);
    edge->addFEdge(fEdge);
    bool inserted = StoreSCGEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new StoreCGEdge not added??");

    srcNode->addOutgoingStoreEdge(edge);
    dstNode->addIncomingStoreEdge(edge);
    return edge;
}

/*!
 * Remove a Store edge
 */
StoreSCGEdge* SConstraintGraph::removeStoreSCGEdgeByFlat(NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    FConstraintNode* fSrcNode = fConsG->getFConstraintNode(src);
    FConstraintNode* fDstNode = fConsG->getFConstraintNode(dst);

    FConstraintEdge* fEdge = fConsG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FStore);
    SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SStore);

    StoreSCGEdge* sStore = SVFUtil::dyn_cast<StoreSCGEdge>(sEdge);
    StoreFCGEdge* fStore = SVFUtil::dyn_cast<StoreFCGEdge>(fEdge);
    sEdge->removeFEdge(fEdge);
    fConsG->removeStoreEdge(fStore);
    if (sEdge->getFEdgeSet().size() == 0)
    {
        removeStoreEdge(sStore);
        return nullptr;
    }
    return sStore;
}

AddrSCGEdge* SConstraintGraph::retargetAddrSCGEdge(AddrSCGEdge* oldSEdge, NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SAddr)) {
         // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SAddr);
        for (auto fEdge: oldSEdge->getFEdgeSet()) 
            sEdge->addFEdge(fEdge);
        removeAddrEdge(oldSEdge);
        
        return nullptr;
    }

    AddrSCGEdge* edge = new AddrSCGEdge(srcNode, dstNode, edgeIndex++);
    for (auto fEdge: oldSEdge->getFEdgeSet())
        edge->addFEdge(fEdge);
    removeAddrEdge(oldSEdge);

    bool inserted = AddrSCGEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new AddrSCGEdge not added??");

    srcNode->addOutgoingAddrEdge(edge);
    dstNode->addIncomingAddrEdge(edge);
    
    return edge;
}

CopySCGEdge* SConstraintGraph::retargetCopySCGEdge(CopySCGEdge* oldSEdge, NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SCopy)) {
         // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SCopy);
        for (auto fEdge: oldSEdge->getFEdgeSet()) 
            sEdge->addFEdge(fEdge);
        removeDirectEdge(oldSEdge);
        
        return nullptr;
    }

    CopySCGEdge* edge = new CopySCGEdge(srcNode, dstNode, edgeIndex++);
    for (auto fEdge: oldSEdge->getFEdgeSet())
        edge->addFEdge(fEdge);
    removeDirectEdge(oldSEdge);

    bool inserted = directSEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new CopySCGEdge not added??");

    srcNode->addOutgoingCopyEdge(edge);
    dstNode->addIncomingCopyEdge(edge);
    
    return edge;
}

NormalGepSCGEdge* SConstraintGraph::retargetNormalGepSCGEdge(NormalGepSCGEdge* oldSEdge, NodeID src, NodeID dst, const AccessPath& ap)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SNormalGep)) {
         // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SNormalGep);
        for (auto fEdge: oldSEdge->getFEdgeSet()) 
            sEdge->addFEdge(fEdge);
        removeDirectEdge(oldSEdge);
        
        return nullptr;
    }

    NormalGepSCGEdge* edge = new NormalGepSCGEdge(srcNode, dstNode, ap, edgeIndex++);
    for (auto fEdge: oldSEdge->getFEdgeSet())
        edge->addFEdge(fEdge);
    removeDirectEdge(oldSEdge);

    bool inserted = directSEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new NormalGepSCGEdge not added??");

    srcNode->addOutgoingGepEdge(edge);
    dstNode->addIncomingGepEdge(edge);
    
    return edge;
}

VariantGepSCGEdge* SConstraintGraph::retargetVariantGepSCGEdge(VariantGepSCGEdge* oldSEdge, NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SVariantGep)) {
         // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SVariantGep);
        for (auto fEdge: oldSEdge->getFEdgeSet()) 
            sEdge->addFEdge(fEdge);
        removeDirectEdge(oldSEdge);
        
        return nullptr;
    }

    VariantGepSCGEdge* edge = new VariantGepSCGEdge(srcNode, dstNode, edgeIndex++);
    for (auto fEdge: oldSEdge->getFEdgeSet())
        edge->addFEdge(fEdge);
    removeDirectEdge(oldSEdge);

    bool inserted = directSEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new VariantGepSCGEdge not added??");

    srcNode->addOutgoingGepEdge(edge);
    dstNode->addIncomingGepEdge(edge);
    
    return edge;
}

LoadSCGEdge* SConstraintGraph::retargetLoadSCGEdge(LoadSCGEdge* oldSEdge, NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SLoad)) {
         // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SLoad);
        for (auto fEdge: oldSEdge->getFEdgeSet()) 
            sEdge->addFEdge(fEdge);
        removeLoadEdge(oldSEdge);
        
        return nullptr;
    }

    LoadSCGEdge* edge = new LoadSCGEdge(srcNode, dstNode, edgeIndex++);
    for (auto fEdge: oldSEdge->getFEdgeSet())
        edge->addFEdge(fEdge);
    removeLoadEdge(oldSEdge);

    bool inserted = LoadSCGEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new LoadSCGEdge not added??");

    srcNode->addOutgoingLoadEdge(edge);
    dstNode->addIncomingLoadEdge(edge);
    
    return edge;
}

StoreSCGEdge* SConstraintGraph::retargetStoreSCGEdge(StoreSCGEdge* oldSEdge, NodeID src, NodeID dst)
{
    SConstraintNode* srcNode = getSConstraintNode(src);
    SConstraintNode* dstNode = getSConstraintNode(dst);
    if (hasEdge(srcNode, dstNode, SConstraintEdge::SStore)) {
         // add flat edge 
        SConstraintEdge* sEdge = getEdge(srcNode, dstNode, SConstraintEdge::SStore);
        for (auto fEdge: oldSEdge->getFEdgeSet()) 
            sEdge->addFEdge(fEdge);
        removeStoreEdge(oldSEdge);
        
        return nullptr;
    }

    StoreSCGEdge* edge = new StoreSCGEdge(srcNode, dstNode, edgeIndex++);
    for (auto fEdge: oldSEdge->getFEdgeSet())
        edge->addFEdge(fEdge);
    removeStoreEdge(oldSEdge);

    bool inserted = StoreSCGEdgeSet.insert(edge).second;
    (void)inserted; // Suppress warning of unused variable under release build
    assert(inserted && "new StoreSCGEdge not added??");

    srcNode->addOutgoingStoreEdge(edge);
    dstNode->addIncomingStoreEdge(edge);
    
    return edge;
}

/*!
 * Re-target dst node of an edge
 *
 * (1) Remove edge from old dst target,
 * (2) Change edge dst id and
 * (3) Add modifed edge into new dst
 */
void SConstraintGraph::reTargetDstOfEdge(SConstraintEdge* edge, SConstraintNode* newDstNode)
{
    NodeID newDstNodeID = newDstNode->getId();
    NodeID srcId = edge->getSrcID();
    if(LoadSCGEdge* load = SVFUtil::dyn_cast<LoadSCGEdge>(edge))
    {
        retargetLoadSCGEdge(load, srcId, newDstNodeID);
        // removeLoadEdge(load);
        // addLoadCGEdge(srcId,newDstNodeID);
    }
    else if(StoreSCGEdge* store = SVFUtil::dyn_cast<StoreSCGEdge>(edge))
    {
        retargetStoreSCGEdge(store, srcId, newDstNodeID);
        // removeStoreEdge(store);
        // addStoreCGEdge(srcId,newDstNodeID);
    }
    else if(CopySCGEdge* copy = SVFUtil::dyn_cast<CopySCGEdge>(edge))
    {
        retargetCopySCGEdge(copy, srcId, newDstNodeID);
        // removeDirectEdge(copy);
        // addCopyCGEdge(srcId,newDstNodeID);
    }
    else if(NormalGepSCGEdge* gep = SVFUtil::dyn_cast<NormalGepSCGEdge>(edge))
    {
        const AccessPath ap = gep->getAccessPath();
        retargetNormalGepSCGEdge(gep, srcId, newDstNodeID, ap);
        // removeDirectEdge(gep);
        // addNormalGepCGEdge(srcId,newDstNodeID, ap);
    }
    else if(VariantGepSCGEdge* gep = SVFUtil::dyn_cast<VariantGepSCGEdge>(edge))
    {
        retargetVariantGepSCGEdge(gep, srcId, newDstNodeID);
        // removeDirectEdge(gep);
        // addVariantGepCGEdge(srcId,newDstNodeID);
    }
    else if(AddrSCGEdge* addr = SVFUtil::dyn_cast<AddrSCGEdge>(edge))
    {
        retargetAddrSCGEdge(addr, srcId, newDstNodeID);
        // removeAddrEdge(addr);
    }
    else
        assert(false && "no other edge type!!");
}

/*!
 * Re-target src node of an edge
 * (1) Remove edge from old src target,
 * (2) Change edge src id and
 * (3) Add modified edge into new src
 */
void SConstraintGraph::reTargetSrcOfEdge(SConstraintEdge* edge, SConstraintNode* newSrcNode)
{
    NodeID newSrcNodeID = newSrcNode->getId();
    NodeID dstId = edge->getDstID();
    if(LoadSCGEdge* load = SVFUtil::dyn_cast<LoadSCGEdge>(edge))
    {
        retargetLoadSCGEdge(load, newSrcNodeID, dstId);
        // removeLoadEdge(load);
        // addLoadCGEdge(newSrcNodeID,dstId);
    }
    else if(StoreSCGEdge* store = SVFUtil::dyn_cast<StoreSCGEdge>(edge))
    {
        retargetStoreSCGEdge(store, newSrcNodeID, dstId);
        // removeStoreEdge(store);
        // addStoreCGEdge(newSrcNodeID,dstId);
    }
    else if(CopySCGEdge* copy = SVFUtil::dyn_cast<CopySCGEdge>(edge))
    {
        retargetCopySCGEdge(copy, newSrcNodeID, dstId);
        // removeDirectEdge(copy);
        // addCopyCGEdge(newSrcNodeID,dstId);
    }
    else if(NormalGepSCGEdge* gep = SVFUtil::dyn_cast<NormalGepSCGEdge>(edge))
    {
        const AccessPath ap = gep->getAccessPath();
        retargetNormalGepSCGEdge(gep, newSrcNodeID, dstId, ap);
        // removeDirectEdge(gep);
        // addNormalGepCGEdge(newSrcNodeID, dstId, ap);
    }
    else if(VariantGepSCGEdge* gep = SVFUtil::dyn_cast<VariantGepSCGEdge>(edge))
    {
        retargetVariantGepSCGEdge(gep, newSrcNodeID, dstId);
        // removeDirectEdge(gep);
        // addVariantGepCGEdge(newSrcNodeID,dstId);
    }
    else if(AddrSCGEdge* addr = SVFUtil::dyn_cast<AddrSCGEdge>(edge))
    {
        retargetAddrSCGEdge(addr, newSrcNodeID, dstId);
        // removeAddrEdge(addr);
    }
    else
        assert(false && "no other edge type!!");
}

/*!
 * Remove addr edge from their src and dst edge sets
 */
void SConstraintGraph::removeAddrEdge(AddrSCGEdge* edge)
{
    getSConstraintNode_d(edge->getSrcID())->removeOutgoingAddrEdge(edge);
    getSConstraintNode_d(edge->getDstID())->removeIncomingAddrEdge(edge);
    u32_t num = AddrSCGEdgeSet.erase(edge);
    (void)num; // Suppress warning of unused variable under release build
    assert(num && "edge not in the set, can not remove!!!");
    delete edge;
}

/*!
 * Remove load edge from their src and dst edge sets
 */
void SConstraintGraph::removeLoadEdge(LoadSCGEdge* edge)
{
    getSConstraintNode_d(edge->getSrcID())->removeOutgoingLoadEdge(edge);
    getSConstraintNode_d(edge->getDstID())->removeIncomingLoadEdge(edge);
    u32_t num = LoadSCGEdgeSet.erase(edge);
    (void)num; // Suppress warning of unused variable under release build
    assert(num && "edge not in the set, can not remove!!!");
    delete edge;
}

/*!
 * Remove store edge from their src and dst edge sets
 */
void SConstraintGraph::removeStoreEdge(StoreSCGEdge* edge)
{
    getSConstraintNode_d(edge->getSrcID())->removeOutgoingStoreEdge(edge);
    getSConstraintNode_d(edge->getDstID())->removeIncomingStoreEdge(edge);
    u32_t num = StoreSCGEdgeSet.erase(edge);
    (void)num; // Suppress warning of unused variable under release build
    assert(num && "edge not in the set, can not remove!!!");
    delete edge;
}

/*!
 * Remove edges from their src and dst edge sets
 */
void SConstraintGraph::removeDirectEdge(SConstraintEdge* edge)
{
    getSConstraintNode_d(edge->getSrcID())->removeOutgoingDirectEdge(edge);
    getSConstraintNode_d(edge->getDstID())->removeIncomingDirectEdge(edge);
    u32_t num = directSEdgeSet.erase(edge);
    (void)num; // Suppress warning of unused variable under release build
    assert(num && "edge not in the set, can not remove!!!");
    delete edge;
}

/*
 * SCC break detection after a direct edge removal
 */
unsigned SConstraintGraph::sccBreakDetect(NodeID src, NodeID dst, FConstraintEdge::FConstraintEdgeK kind, NodeBS& allReps, NodeID& oldRep)
{
    enum {SCC_RESTORE, SCC_KEEP};
    if (src == 5915 && dst == 320798 && kind == FConstraintEdge::FCopy)
    {
        src = src;
    }
    SConstraintEdge::SConstraintEdgeK skind = F2SKind(kind);
    NodeID rep1 = sccRepNode(src);
    NodeID rep2 = sccRepNode(dst);
    assert(rep1 == rep2 && "sccBreakDetect only for edge in scc!\n");

    NodeID rep = rep1;
    SConstraintNode* originRepNode = getSConstraintNode(rep);

    oldRep = rep;
    ConstraintGraph* tempG = buildTempG(rep, src, dst, kind);
    SCCDetection<ConstraintGraph*> d(tempG);
    d.find();
    delete tempG;
    NodeStack & topoOrder = d.topoNodeStack();
    if (topoOrder.size() > 1) {
        // TODO: ReDetect the sub scc --wjy
        // SCC broken
        // sccRestore(rep);
        // NOTE: The edge to be removed is still in fCG and SCG ! 

        // 1. reset rep/sub relation
        NodeBS allSubs = sccSubNodes(rep);
        resetSubs(rep);
        for (NodeID sub: allSubs)
            resetRep(sub);

        while (!topoOrder.empty())
        {
            NodeID repNodeId = topoOrder.top();
            topoOrder.pop();

            // collect new reps
            allReps.set(repNodeId);

            // {@ set new rep/sub relation
            const NodeBS& subNodes = d.subNodes(repNodeId);
            NodeBS subNodesNotConst;
            for (NodeBS::iterator nodeIt = subNodes.begin(); nodeIt != subNodes.end(); nodeIt++)
            {
                
                NodeID subNodeId = *nodeIt;
                subNodesNotConst.set(subNodeId);
                if (subNodeId != repNodeId)
                {
                    setRep(subNodeId, repNodeId);
                    // subNodeId has no subs node
                }
            }
            setSubs(repNodeId, subNodesNotConst);
            // @}
        }

        // 2. restore sconstraint node
        for (NodeBS::iterator nodeIt = allReps.begin(); nodeIt != allReps.end(); nodeIt ++)
        {
            NodeID eachRep = *nodeIt;

            // Add new rep node into SCG
            if (eachRep != rep)
                addSConstraintNode(new SConstraintNode(eachRep), eachRep);
        }
        
        // 3. restore sconstriant edge for each new rep node
        /// 3.1 collect all sEdges and fEdges;
        /// 3.2 remove sEdges
        /// 3.3 add fEdges
        // for (NodeBS::iterator nodeIt = allReps.begin(); nodeIt != allReps.end(); nodeIt ++)
        // {
        //     NodeID eachRep = *nodeIt;
        //     SConstraintNode* repNode = getSConstraintNode(eachRep);
        //     restoreEdge(repNode);
        // }
        restoreEdge(originRepNode);
        if (!allReps.test(rep))
            removeSConstraintNode(originRepNode);

        // 4. remove target fEdge and sEdge
        FConstraintNode* srcFNode = fConsG->getFConstraintNode(src);
        FConstraintNode* dstFNode = fConsG->getFConstraintNode(dst);
        FConstraintEdge* fEdge = fConsG->getEdge(srcFNode, dstFNode, kind);
        SConstraintNode* srcSNode = getSConstraintNode(src);
        SConstraintNode* dstSNode = getSConstraintNode(dst);
        SConstraintEdge* sEdge = getEdge(srcSNode, dstSNode, skind);
        
        removeDirectEdge(sEdge);
        fConsG->removeDirectEdge(fEdge);

        return SCC_RESTORE;    
    }
    else {
        // SCC keep
        SConstraintNode* repSNode = getSConstraintNode(rep);
        SConstraintEdge* sEdge = getEdge(repSNode, repSNode, skind);
        FConstraintNode* srcFNode = fConsG->getFConstraintNode(src);
        FConstraintNode* dstFNode = fConsG->getFConstraintNode(dst);
        FConstraintEdge* fEdge = fConsG->getEdge(srcFNode, dstFNode, kind);
        // NOTE: remove the edge in both fCG and SCG;
        sEdge->removeFEdge(fEdge);
        fConsG->removeDirectEdge(fEdge);
        return SCC_KEEP;
    }
    
    
}

ConstraintGraph* SConstraintGraph::buildTempG(NodeID rep, NodeID src, NodeID dst, FConstraintEdge::FConstraintEdgeK kind)
{
    ConstraintGraph* g = new ConstraintGraph();
    SConstraintNode* repSNode = getSConstraintNode(rep);

    NodeBS nodes;
    nodes.set(rep);
    nodes |= sccSubNodes(rep);
    for (NodeID nodeId: nodes)
        g->addConstraintNode(new ConstraintNode(nodeId), nodeId);
    
    for (auto it = repSNode->directOutEdgeBegin(), eit = repSNode->directOutEdgeEnd();
        it != eit; ++it)
    {
        SConstraintEdge* sEdge = *it;
        if (sEdge->getDstID() == rep) {
            for (FConstraintEdge* fEdge: sEdge->getFEdgeSet()) {
                NodeID fsrc = fEdge->getSrcID();
                NodeID fdst = fEdge->getDstID();
                // FConstraintEdge::FConstraintEdgeK fkind = fEdge->getEdgeKind();
                if (SVFUtil::isa<CopyFCGEdge>(fEdge)) {
                    if (fsrc == src && fdst == dst && kind == FConstraintEdge::FCopy)
                        continue;
                    g->addCopyCGEdge(fsrc, fdst);
                }
                else if (SVFUtil::isa<NormalGepFCGEdge>(fEdge)) {
                    if (fsrc == src && fdst == dst && kind == FConstraintEdge::FNormalGep)
                        continue;
                    NormalGepFCGEdge* fgep = SVFUtil::dyn_cast<NormalGepFCGEdge>(fEdge);
                    g->addNormalGepCGEdge(fsrc, fdst, fgep->getAccessPath());
                }
                else if (SVFUtil::isa<VariantGepFCGEdge>(fEdge)) {
                    if (fsrc == src && fdst == dst && kind == FConstraintEdge::FVariantGep)
                        continue;
                    g->addVariantGepCGEdge(fsrc, fdst);
                }
                // if (fsrc == src && fdst == dst && fkind == kind)
                //     continue; // assume the fEdge is deleted
                // switch (fkind) {
                //     case FConstraintEdge::FCopy:
                //         g->addCopyCGEdge(fsrc, fdst);
                //         break;
                //     case FConstraintEdge::FVariantGep:
                //         g->addVariantGepCGEdge(fsrc, fdst);
                //         break;
                //     case FConstraintEdge::FNormalGep:
                        // NormalGepFCGEdge* fgep = SVFUtil::dyn_cast<NormalGepFCGEdge>(fEdge);
                        // g->addNormalGepCGEdge(fsrc, fdst, fgep->getAccessPath());
                //         break;
                // }
            }
        }
    }
    return g;
}

void SConstraintGraph::sccRestore(NodeID rep)
{
    // 1. reset rep/sub relation
    NodeBS& subs = sccSubNodes(rep);
    resetSubs(rep);
    for (NodeID sub: subs)
        resetRep(sub);

    SConstraintNode* repNode = getSConstraintNode(rep);

    // 2. restore sconstraint node
    for (NodeID sub: subs)
        addSConstraintNode(new SConstraintNode(sub), sub);

    // 3. restore sconstriant edge
    /// 3.1 collect all sEdges and fEdges;
    /// 3.2 remove sEdges
    /// 3.3 add fEdges
    restoreEdge(repNode);
}

void SConstraintGraph::restoreEdge(SConstraintNode* repNode)
{
    // 3. restore sconstriant edge
    /// 3.1 collect all sEdges and fEdges;
    SConstraintEdge::SConstraintEdgeSetTy sEdges;
    FConstraintEdge::FConstraintEdgeSetTy fEdges;
    for (auto it = repNode->InEdgeBegin(), eit = repNode->InEdgeEnd();
        it != eit; ++it) {
        SConstraintEdge* sEdge = *it;
        sEdges.insert(sEdge);
        for (FConstraintEdge* fEdge: sEdge->getFEdgeSet())
            fEdges.insert(fEdge);
    }
    for (auto it = repNode->OutEdgeBegin(), eit = repNode->OutEdgeEnd();
        it != eit; ++it) {
        SConstraintEdge* sEdge = *it;
        sEdges.insert(sEdge);
        for (FConstraintEdge* fEdge: sEdge->getFEdgeSet())
            fEdges.insert(fEdge);
    }
    /// 3.2 remove sEdges
    for (SConstraintEdge* sEdge: sEdges) {
        if (SVFUtil::isa<AddrSCGEdge>(sEdge)) {
            AddrSCGEdge* sAddr = SVFUtil::dyn_cast<AddrSCGEdge>(sEdge);
            removeAddrEdge(sAddr);
        }
        else if (SVFUtil::isa<CopySCGEdge>(sEdge)) {
            // CopySCGEdge* sCopy = SVFUtil::dyn_cast<CopySCGEdge>(sEdge);
            removeDirectEdge(sEdge);
        }
        else if (SVFUtil::isa<LoadSCGEdge>(sEdge)) {
            LoadSCGEdge* sLoad = SVFUtil::dyn_cast<LoadSCGEdge>(sEdge);
            removeLoadEdge(sLoad);
        }
        else if (SVFUtil::isa<StoreSCGEdge>(sEdge)) {
            StoreSCGEdge* sStore = SVFUtil::dyn_cast<StoreSCGEdge>(sEdge);
            removeStoreEdge(sStore);
        }
        else if (SVFUtil::isa<NormalGepSCGEdge>(sEdge)) {
            // NormalGepSCGEdge* sngep = SVFUtil::dyn_cast<NormalGepSCGEdge>(sEdge);
            removeDirectEdge(sEdge);
        }
        else if (SVFUtil::isa<VariantGepSCGEdge>(sEdge)) {
            // NormalGepSCGEdge* sngep = SVFUtil::dyn_cast<NormalGepSCGEdge>(sEdge);
            removeDirectEdge(sEdge);
        }
    }
    /// 3.3 add fEdges
    for (FConstraintEdge* fEdge: fEdges) {
        NodeID fsrc = fEdge->getSrcID();
        NodeID fdst = fEdge->getDstID();
        if (SVFUtil::isa<AddrFCGEdge>(fEdge))
            addAddrSCGEdge(fsrc, fdst);
        else if (SVFUtil::isa<CopyFCGEdge>(fEdge))
            addCopySCGEdge(fsrc, fdst, true);
        else if (SVFUtil::isa<LoadFCGEdge>(fEdge))
            addLoadSCGEdge(fsrc, fdst);
        else if (SVFUtil::isa<StoreFCGEdge>(fEdge))
            addStoreSCGEdge(fsrc, fdst);
        else if (SVFUtil::isa<VariantGepFCGEdge>(fEdge))
            addVariantGepSCGEdge(fsrc, fdst);
        else if (SVFUtil::isa<NormalGepFCGEdge>(fEdge)) {
            NormalGepFCGEdge* fngep = SVFUtil::dyn_cast<NormalGepFCGEdge>(fEdge);
            addNormalGepSCGEdge(fsrc, fdst, fngep->getAccessPath());
        }
    }
}

/*!
 * Move incoming direct edges of a sub node which is outside SCC to its rep node
 * Remove incoming direct edges of a sub node which is inside SCC from its rep node
 */
bool SConstraintGraph::moveInEdgesToRepNode(SConstraintNode* node, SConstraintNode* rep )
{
    std::vector<SConstraintEdge*> sccEdges;
    std::vector<SConstraintEdge*> nonSccEdges;
    for (SConstraintNode::const_iterator it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit;
            ++it)
    {
        SConstraintEdge* subInEdge = *it;
        if(sccRepNode(subInEdge->getSrcID()) != rep->getId())
            nonSccEdges.push_back(subInEdge);
        else
        {
            sccEdges.push_back(subInEdge);
        }
    }
    // if this edge is outside scc, then re-target edge dst to rep
    while(!nonSccEdges.empty())
    {
        SConstraintEdge* edge = nonSccEdges.back();
        nonSccEdges.pop_back();
        reTargetDstOfEdge(edge,rep);
    }

    bool criticalGepInsideSCC = false;
    // if this edge is inside scc, then remove this edge and two end nodes
    /// wjy TODO: Should super constraint edges be removed directly?
    while(!sccEdges.empty())
    {
        SConstraintEdge* edge = sccEdges.back();
        sccEdges.pop_back();
        /// only copy and gep edge can be removed
        if(SVFUtil::isa<CopySCGEdge>(edge)) {
            // removeDirectEdge(edge);
            reTargetDstOfEdge(edge, rep);
        }
            
        else if (SVFUtil::isa<GepSCGEdge>(edge))
        {
            // If the GEP is critical (i.e. may have a non-zero offset),
            // then it brings impact on field-sensitivity.
            if (!isZeroOffsettedGepSCGEdge(edge))
            {
                criticalGepInsideSCC = true;
            }
            // removeDirectEdge(edge);
            reTargetDstOfEdge(edge, rep);
        }
        else if(SVFUtil::isa<LoadSCGEdge, StoreSCGEdge>(edge))
            reTargetDstOfEdge(edge,rep);
        else if(AddrSCGEdge* addr = SVFUtil::dyn_cast<AddrSCGEdge>(edge))
        {
            // removeAddrEdge(addr);
            reTargetDstOfEdge(edge, rep);
        }
        else
            assert(false && "no such edge");
    }
    return criticalGepInsideSCC;
}

/*!
 * Move outgoing direct edges of a sub node which is outside SCC to its rep node
 * Remove outgoing direct edges of a sub node which is inside SCC from its rep node
 */
bool SConstraintGraph::moveOutEdgesToRepNode(SConstraintNode*node, SConstraintNode* rep )
{

    std::vector<SConstraintEdge*> sccEdges;
    std::vector<SConstraintEdge*> nonSccEdges;

    for (SConstraintNode::const_iterator it = node->OutEdgeBegin(), eit = node->OutEdgeEnd(); it != eit;
            ++it)
    {
        SConstraintEdge* subOutEdge = *it;
        if(sccRepNode(subOutEdge->getDstID()) != rep->getId())
            nonSccEdges.push_back(subOutEdge);
        else
        {
            sccEdges.push_back(subOutEdge);
        }
    }
    // if this edge is outside scc, then re-target edge src to rep
    while(!nonSccEdges.empty())
    {
        SConstraintEdge* edge = nonSccEdges.back();
        nonSccEdges.pop_back();
        reTargetSrcOfEdge(edge,rep);
    }
    bool criticalGepInsideSCC = false;
    // if this edge is inside scc, then remove this edge and two end nodes
    /// wjy TODO: Should super constraint edges be removed directly?
    while(!sccEdges.empty())
    {
        SConstraintEdge* edge = sccEdges.back();
        sccEdges.pop_back();
        /// only copy and gep edge can be removed
        if(SVFUtil::isa<CopySCGEdge>(edge)) {
            // removeDirectEdge(edge);
            reTargetSrcOfEdge(edge, rep);
        }
            
        else if (SVFUtil::isa<GepSCGEdge>(edge))
        {
            // If the GEP is critical (i.e. may have a non-zero offset),
            // then it brings impact on field-sensitivity.
            if (!isZeroOffsettedGepSCGEdge(edge))
            {
                criticalGepInsideSCC = true;
            }
            // removeDirectEdge(edge);
            reTargetSrcOfEdge(edge, rep);
        }
        else if(SVFUtil::isa<LoadSCGEdge, StoreSCGEdge>(edge))
            reTargetSrcOfEdge(edge,rep);
        else if(AddrSCGEdge* addr = SVFUtil::dyn_cast<AddrSCGEdge>(edge))
        {
            // removeAddrEdge(addr);
            reTargetSrcOfEdge(edge, rep);
        }
        else
            assert(false && "no such edge");
    }
    return criticalGepInsideSCC;
}

/*!
 * Dump super constraint graph
 */
void SConstraintGraph::dump(std::string name)
{
    GraphPrinter::WriteGraphToFile(outs(), name, this);
}

/*!
 * Print this constraint graph including its nodes and edges
 */
void SConstraintGraph::print()
{

    outs() << "-----------------SConstraintGraph--------------------------------------\n";

    SConstraintEdge::SConstraintEdgeSetTy& addrs = this->getAddrSCGEdges();
    for (SConstraintEdge::SConstraintEdgeSetTy::iterator iter = addrs.begin(),
            eiter = addrs.end(); iter != eiter; ++iter)
    {
        outs() << (*iter)->getSrcID() << " -- SAddr --> " << (*iter)->getDstID()
               << "\n";
    }

    SConstraintEdge::SConstraintEdgeSetTy& directs = this->getDirectSCGEdges();
    for (SConstraintEdge::SConstraintEdgeSetTy::iterator iter = directs.begin(),
            eiter = directs.end(); iter != eiter; ++iter)
    {
        if (CopySCGEdge* copy = SVFUtil::dyn_cast<CopySCGEdge>(*iter))
        {
            outs() << copy->getSrcID() << " -- SCopy --> " << copy->getDstID()
                   << "\n";
        }
        else if (NormalGepSCGEdge* ngep = SVFUtil::dyn_cast<NormalGepSCGEdge>(*iter))
        {
            outs() << ngep->getSrcID() << " -- SNormalGep (" << ngep->getConstantFieldIdx()
                   << ") --> " << ngep->getDstID() << "\n";
        }
        else if (VariantGepSCGEdge* vgep = SVFUtil::dyn_cast<VariantGepSCGEdge>(*iter))
        {
            outs() << vgep->getSrcID() << " -- SVarintGep --> "
                   << vgep->getDstID() << "\n";
        }
        else
            assert(false && "wrong constraint edge kind!");
    }

    SConstraintEdge::SConstraintEdgeSetTy& loads = this->getLoadSCGEdges();
    for (SConstraintEdge::SConstraintEdgeSetTy::iterator iter = loads.begin(),
            eiter = loads.end(); iter != eiter; ++iter)
    {
        outs() << (*iter)->getSrcID() << " -- SLoad --> " << (*iter)->getDstID()
               << "\n";
    }

    SConstraintEdge::SConstraintEdgeSetTy& stores = this->getStoreSCGEdges();
    for (SConstraintEdge::SConstraintEdgeSetTy::iterator iter = stores.begin(),
            eiter = stores.end(); iter != eiter; ++iter)
    {
        outs() << (*iter)->getSrcID() << " -- SStore --> " << (*iter)->getDstID()
               << "\n";
    }

    outs()
            << "--------------------------------------------------------------\n";

}

/*!
 * View dot graph of Constraint graph from debugger.
 */
void SConstraintGraph::view()
{
    SVF::ViewGraph(this, "Super Constraint Graph");
}

/// Iterators of direct edges for ConsGNode
//@{
SConstraintNode::iterator SConstraintNode::directOutEdgeBegin()
{
    if (Options::DetectPWC())
        return directOutEdges.begin();
    else
        return copyOutEdges.begin();
}

SConstraintNode::iterator SConstraintNode::directOutEdgeEnd()
{
    if (Options::DetectPWC())
        return directOutEdges.end();
    else
        return copyOutEdges.end();
}

SConstraintNode::iterator SConstraintNode::directInEdgeBegin()
{
    if (Options::DetectPWC())
        return directInEdges.begin();
    else
        return copyInEdges.begin();
}

SConstraintNode::iterator SConstraintNode::directInEdgeEnd()
{
    if (Options::DetectPWC())
        return directInEdges.end();
    else
        return copyInEdges.end();
}

SConstraintNode::const_iterator SConstraintNode::directOutEdgeBegin() const
{
    if (Options::DetectPWC())
        return directOutEdges.begin();
    else
        return copyOutEdges.begin();
}

SConstraintNode::const_iterator SConstraintNode::directOutEdgeEnd() const
{
    if (Options::DetectPWC())
        return directOutEdges.end();
    else
        return copyOutEdges.end();
}

SConstraintNode::const_iterator SConstraintNode::directInEdgeBegin() const
{
    if (Options::DetectPWC())
        return directInEdges.begin();
    else
        return copyInEdges.begin();
}

SConstraintNode::const_iterator SConstraintNode::directInEdgeEnd() const
{
    if (Options::DetectPWC())
        return directInEdges.end();
    else
        return copyInEdges.end();
}
//@}

/*!
 * GraphTraits specialization for constraint graph
 */
namespace SVF
{
template<>
struct DOTGraphTraits<SConstraintGraph*> : public DOTGraphTraits<SVFIR*>
{

    typedef SConstraintNode NodeType;
    DOTGraphTraits(bool isSimple = false) :
        DOTGraphTraits<SVFIR*>(isSimple)
    {
    }

    /// Return name of the graph
    static std::string getGraphName(SConstraintGraph*)
    {
        return "SConstraintG";
    }

    static bool isNodeHidden(NodeType *n, SConstraintGraph *)
    {
        if (Options::ShowHiddenNode()) return false;
        else return (n->getInEdges().empty() && n->getOutEdges().empty());
    }

    /// Return label of a VFG node with two display mode
    /// Either you can choose to display the name of the value or the whole instruction
    static std::string getNodeLabel(NodeType *n, SConstraintGraph*)
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

    static std::string getNodeAttributes(NodeType *n, SConstraintGraph*)
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
    static std::string getEdgeAttributes(NodeType*, EdgeIter EI, SConstraintGraph*)
    {
        SConstraintEdge* edge = *(EI.getCurrent());
        assert(edge && "No edge found!!");
        if (edge->getEdgeKind() == SConstraintEdge::SAddr)
        {
            return "color=green";
        }
        else if (edge->getEdgeKind() == SConstraintEdge::SCopy)
        {
            return "color=black";
        }
        else if (edge->getEdgeKind() == SConstraintEdge::SNormalGep
                 || edge->getEdgeKind() == SConstraintEdge::SVariantGep)
        {
            return "color=purple";
        }
        else if (edge->getEdgeKind() == SConstraintEdge::SStore)
        {
            return "color=blue";
        }
        else if (edge->getEdgeKind() == SConstraintEdge::SLoad)
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
