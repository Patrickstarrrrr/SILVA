#include "WPA/AndersenInc.h"
#include "MemoryModel/PointsTo.h"
#include "Util/Options.h"
#include "Graphs/CHG.h"
#include "Util/SVFUtil.h"
#include "MemoryModel/PointsTo.h"
#include "WPA/Steensgaard.h"
// #include "AndersenInc.h"

using namespace SVF;
using namespace SVFUtil;
using namespace std;

AndersenInc* AndersenInc::incpta = nullptr;

u32_t AndersenInc::numOfProcessedAddr = 0;
u32_t AndersenInc::numOfProcessedCopy = 0;
u32_t AndersenInc::numOfProcessedGep = 0;
u32_t AndersenInc::numOfProcessedLoad = 0;
u32_t AndersenInc::numOfProcessedStore = 0;
u32_t AndersenInc::numOfSfrs = 0;
u32_t AndersenInc::numOfFieldExpand = 0;

u32_t AndersenInc::numOfSCCDetection = 0;
double AndersenInc::timeOfSCCDetection = 0;
double AndersenInc::timeOfSCCMerges = 0;
double AndersenInc::timeOfCollapse = 0;

u32_t AndersenInc::AveragePointsToSetSize = 0;
u32_t AndersenInc::MaxPointsToSetSize = 0;
double AndersenInc::timeOfProcessCopyGep = 0;
double AndersenInc::timeOfProcessLoadStore = 0;
double AndersenInc::timeOfUpdateCallGraph = 0;

/*!
 * Initialize
 */
void AndersenInc::initialize()
{
    ///@ Andersen::initialize() {
    resetData();
    ///@@ AndersenBase::initialize() {

    PointerAnalysis::initialize();
    // ///@@@ PointerAnalysis::initialize() {
    // // assert(pag && "SVFIR has not been built!");
    // svfMod = pag->getModule();
    // chgraph = pag->getCHG();

    // PTACallGraph* cg = new PTACallGraph();
    // CallGraphBuilder bd(cg,pag->getICFG());
    // ptaCallGraph = bd.buildCallGraph(pag->getModule());

    // callGraphSCCDetection();
    // if (Options::CallGraphDotGraph())
    //     getPTACallGraph()->dump("callgraph_initial");
    // ///@@@ } PointerAnalysis::initialize()

    // consCG = new ConstraintGraph(pag);
    fCG = new FConstraintGraph(pag);
    sCG = new SConstraintGraph(pag, fCG);
    setGraph(sCG);
    stat = new AndersenIncStat(this);
    if (Options::ConsCGDotGraph())
        sCG->dump("SConsCG_initial");
    ///@@ } AndersenBase::initialize()

    processAllAddr();
    ///@ } Andersen::intialize()



    setDetectPWC(true);   // Standard wave propagation always collapses PWCs
}

SVF::AndersenInc::~AndersenInc()
{
    delete sCG;
    sCG = nullptr;
    delete fCG;
    fCG = nullptr;
}

void AndersenInc::finalize()
{
    // AndersenBase::finalize()
    if (Options::ConsCGDotGraph())
        sCG->dump("SconsCG_final");

    if (Options::PrintCGGraph())
        sCG->print();
    BVDataPTAImpl::finalize();
}

void AndersenInc::analyze()
{
    initialize();

    // if(!readResultsFromFile)
    // {
    // Start solving constraints
    DBOUT(DGENERAL, outs() << SVFUtil::pasMsg("Start Solving Constraints\n"));

    bool limitTimerSet = SVFUtil::startAnalysisLimitTimer(Options::AnderTimeLimit());

    initWorklist();
    do
    {
        numOfIteration++;
        if (0 == numOfIteration % iterationForPrintStat)
            printStat();

        reanalyze = false;

        solveWorklist();

        if (updateCallGraph(getIndirectCallsites()))
            reanalyze = true;

    }
    while (reanalyze);

    // Analysis is finished, reset the alarm if we set it.
    SVFUtil::stopAnalysisLimitTimer(limitTimerSet);

    DBOUT(DGENERAL, outs() << SVFUtil::pasMsg("Finish Solving Constraints\n"));

    // }

    // if (!readResultsFromFile)
        // Finalize the analysis
    processDeletion();
    finalize();
}


void AndersenInc::cleanConsCG(NodeID id)
{
    sCG->resetSubs(sCG->getRep(id));
    for (NodeID sub: sCG->getSubs(id))
        sCG->resetRep(sub);
    sCG->resetSubs(id);
    sCG->resetRep(id);
    assert(!sCG->hasGNode(id) && "this is either a rep nodeid or a sub nodeid should have already been merged to its field-insensitive base! ");
}

void AndersenInc::normalizePointsTo()
{
    SVFIR::MemObjToFieldsMap &memToFieldsMap = pag->getMemToFieldsMap();
    SVFIR::NodeOffsetMap &GepObjVarMap = pag->getGepObjNodeMap();

    // clear GepObjVarMap/memToFieldsMap/nodeToSubsMap/nodeToRepMap
    // for redundant gepnodes and remove those nodes from pag
    for (NodeID n: redundantGepNodes)
    {
        NodeID base = pag->getBaseObjVar(n);
        GepObjVar *gepNode = SVFUtil::dyn_cast<GepObjVar>(pag->getGNode(n));
        assert(gepNode && "Not a gep node in redundantGepNodes set");
        const APOffset apOffset = gepNode->getConstantFieldIdx();
        GepObjVarMap.erase(std::make_pair(base, apOffset));
        memToFieldsMap[base].reset(n);
        cleanConsCG(n);

        pag->removeGNode(gepNode);
    }
}

/*!
 * Process copy and gep edges
 */
void AndersenInc::handleCopyGep(SConstraintNode* node)
{
    NodeID nodeId = node->getId();
    computeDiffPts(nodeId);

    if (!getDiffPts(nodeId).empty())
    {
        for (SConstraintEdge* edge : node->getCopyOutEdges()) 
        {
            NodeID dstId = edge->getDstID();
            if (nodeId != dstId)
                processCopy(nodeId, edge);
        }
        for (SConstraintEdge* edge : node->getGepOutEdges())
        {
            if (GepSCGEdge* gepEdge = SVFUtil::dyn_cast<GepSCGEdge>(edge)) {
                NodeID dstId = gepEdge->getDstID();
                if (nodeId != dstId)
                    processGep(nodeId, gepEdge);
                // TOOD: gep inside scc --wjy
            }
        }
    }
}

/*!
 * Process load and store edges
 */
void AndersenInc::handleLoadStore(SConstraintNode *node)
{
    NodeID nodeId = node->getId();
    for (PointsTo::iterator piter = getPts(nodeId).begin(), epiter =
                getPts(nodeId).end(); piter != epiter; ++piter)
    {
        NodeID ptd = *piter;
        // handle load
        for (SConstraintNode::const_iterator it = node->outgoingLoadsBegin(),
                eit = node->outgoingLoadsEnd(); it != eit; ++it)
        {
            if (processLoad(ptd, *it))
                pushIntoWorklist(ptd);
        }

        // handle store
        for (SConstraintNode::const_iterator it = node->incomingStoresBegin(),
                eit = node->incomingStoresEnd(); it != eit; ++it)
        {
            if (processStore(ptd, *it))
                pushIntoWorklist((*it)->getSrcID());
        }
    }
}

/*!
 * Process address edges
 */
void AndersenInc::processAllAddr()
{
    for (SConstraintGraph::const_iterator nodeIt = sCG->begin(), nodeEit = sCG->end(); nodeIt != nodeEit; nodeIt++)
    {
        SConstraintNode*  cgNode = nodeIt->second;
        for (SConstraintNode::const_iterator it = cgNode->incomingAddrsBegin(), eit = cgNode->incomingAddrsEnd();
                it != eit; ++it)
            processAddr(SVFUtil::cast<AddrSCGEdge>(*it));
    }
}

/*!
 * Process address edges
 */
void AndersenInc::processAddr(const AddrSCGEdge* addr)
{
    numOfProcessedAddr++;

    NodeID dst = addr->getDstID();
    NodeID src = addr->getSrcID();
    if(addPts(dst,src))
        pushIntoWorklist(dst);
}



/*!
 * Process load edges
 *	src --load--> dst,
 *	node \in pts(src) ==>  node--copy-->dst
 */
bool AndersenInc::processLoad(NodeID node, const SConstraintEdge* load)
{
    /// TODO: New copy edges are also added for black hole obj node to
    ///       make gcc in spec 2000 pass the flow-sensitive analysis.
    ///       Try to handle black hole obj in an appropiate way.
//	if (pag->isBlkObjOrConstantObj(node) || isNonPointerObj(node))
    if (pag->isConstantObj(node) || isNonPointerObj(node))
        return false;

    numOfProcessedLoad++;

    // process all flat edges
    bool addnew = false;
    for (auto it = load->getFEdgeSet().begin(), eit = load->getFEdgeSet().end(); it != eit; ++it)
    {
        FConstraintEdge* fLoad = *it;
        NodeID fsrc = node;
        NodeID fdst = fLoad->getDstID();
        addnew |= addCopyEdgeByComplexEdge(fsrc, fdst, fLoad);
    }
    
    return addnew;
    // NodeID dst = load->getDstID();
    // return addCopyEdge(node, dst);
}

/*!
 * Process store edges
 *	src --store--> dst,
 *	node \in pts(dst) ==>  src--copy-->node
 */
bool AndersenInc::processStore(NodeID node, const SConstraintEdge* store)
{
    /// TODO: New copy edges are also added for black hole obj node to
    ///       make gcc in spec 2000 pass the flow-sensitive analysis.
    ///       Try to handle black hole obj in an appropiate way
//	if (pag->isBlkObjOrConstantObj(node) || isNonPointerObj(node))
    if (pag->isConstantObj(node) || isNonPointerObj(node))
        return false;

    numOfProcessedStore++;

    bool addnew = false;
    for (auto it = store->getFEdgeSet().begin(), eit = store->getFEdgeSet().end(); it != eit; ++it)
    {
        FConstraintEdge* fStore = *it;
        NodeID fsrc = fStore->getSrcID();
        NodeID fdst = node;
        addnew |= addCopyEdgeByComplexEdge(fsrc, fdst, fStore);
    }
    return addnew;
    // NodeID src = store->getSrcID();
    // return addCopyEdge(src, node);
}

bool AndersenInc::addCopyEdgeByComplexEdge(NodeID fsrc, NodeID fdst, FConstraintEdge* complexEdge)
{
    fCG->addCopyFCGEdge(fsrc, fdst, complexEdge);
    if (sCG->addCopySCGEdge(fsrc, fdst))
    {
        updatePropaPts(fsrc, fdst);
        return true;
    }
    return false;
}

/*!
 * Process copy edges
 *	src --copy--> dst,
 *	union pts(dst) with pts(src)
 */
bool AndersenInc::processCopy(NodeID node, const SConstraintEdge* edge)
{
    numOfProcessedCopy++;

    assert((SVFUtil::isa<CopySCGEdge>(edge)) && "not copy/call/ret ??");
    NodeID dst = edge->getDstID();
    const PointsTo& srcPts = getDiffPts(node);

    bool changed = unionPts(dst, srcPts);
    if (changed)
        pushIntoWorklist(dst);
    return changed;
}

/*!
 * Process gep edges
 *	src --gep--> dst,
 *	for each srcPtdNode \in pts(src) ==> add fieldSrcPtdNode into tmpDstPts
 *		union pts(dst) with tmpDstPts
 */
bool AndersenInc::processGep(NodeID, const GepSCGEdge* edge)
{
    const PointsTo& srcPts = getDiffPts(edge->getSrcID());
    return processGepPts(srcPts, edge);
}

/*!
 * Compute points-to for gep edges
 */
bool AndersenInc::processGepPts(const PointsTo& pts, const GepSCGEdge* edge)
{
    numOfProcessedGep++;

    PointsTo tmpDstPts;
    if (SVFUtil::isa<VariantGepSCGEdge>(edge))
    {
        // If a pointer is connected by a variant gep edge,
        // then set this memory object to be field insensitive,
        // unless the object is a black hole/constant.
        for (NodeID o : pts)
        {
            if (sCG->isBlkObjOrConstantObj(o))
            {
                tmpDstPts.set(o);
                continue;
            }

            if (!isFieldInsensitive(o))
            {
                setObjFieldInsensitive(o);
                sCG->addNodeToBeCollapsed(sCG->getBaseObjVar(o));
            }

            // Add the field-insensitive node into pts.
            NodeID baseId = sCG->getFIObjVar(o);
            tmpDstPts.set(baseId);
        }
    }
    else if (const NormalGepSCGEdge* normalGepEdge = SVFUtil::dyn_cast<NormalGepSCGEdge>(edge))
    {
        // TODO: after the node is set to field insensitive, handling invariant
        // gep edge may lose precision because offsets here are ignored, and the
        // base object is always returned.
        for (NodeID o : pts)
        {
            if (sCG->isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
            {
                tmpDstPts.set(o);
                continue;
            }
            // addGepObjVar for fCG firstly, then addGepObjVar for sCG
            fCG->getGepObjVar(o,normalGepEdge->getAccessPath().getConstantFieldIdx());
            NodeID fieldSrcPtdNode = sCG->getGepObjVar(o, normalGepEdge->getAccessPath().getConstantFieldIdx());
            tmpDstPts.set(fieldSrcPtdNode);
        }
    }
    else
    {
        assert(false && "Andersen::processGepPts: New type GEP edge type?");
    }

    NodeID dstId = edge->getDstID();
    if (unionPts(dstId, tmpDstPts))
    {
        pushIntoWorklist(dstId);
        return true;
    }

    return false;
}

/**
 * Detect and collapse PWC nodes produced by processing gep edges, under the constraint of field limit.
 */
inline void AndersenInc::collapsePWCNode(NodeID nodeId)
{
    // If a node is a PWC node, collapse all its points-to tarsget.
    // collapseNodePts() may change the points-to set of the nodes which have been processed
    // before, in this case, we may need to re-do the analysis.
    if (sCG->isPWCNode(nodeId) && collapseNodePts(nodeId))
        reanalyze = true;
}

inline void AndersenInc::collapseFields()
{
    while (sCG->hasNodesToBeCollapsed())
    {
        NodeID node = sCG->getNextCollapseNode();
        // collapseField() may change the points-to set of the nodes which have been processed
        // before, in this case, we may need to re-do the analysis.
        if (collapseField(node))
            reanalyze = true;
    }
}

/*
 * Merge constraint graph nodes based on SCC cycle detected.
 */
void AndersenInc::mergeSccCycle()
{
    NodeStack revTopoOrder;
    NodeStack & topoOrder = getSCCDetector()->topoNodeStack();
    while (!topoOrder.empty())
    {
        NodeID repNodeId = topoOrder.top();
        topoOrder.pop();
        revTopoOrder.push(repNodeId);
        const NodeBS& subNodes = getSCCDetector()->subNodes(repNodeId);
        // merge sub nodes to rep node
        mergeSccNodes(repNodeId, subNodes);
    }

    // restore the topological order for later solving.
    while (!revTopoOrder.empty())
    {
        NodeID nodeId = revTopoOrder.top();
        revTopoOrder.pop();
        topoOrder.push(nodeId);
    }
}

/**
 * Union points-to of subscc nodes into its rep nodes
 * Move incoming/outgoing direct edges of sub node to rep node
 */
void AndersenInc::mergeSccNodes(NodeID repNodeId, const NodeBS& subNodes)
{
    for (NodeBS::iterator nodeIt = subNodes.begin(); nodeIt != subNodes.end(); nodeIt++)
    {
        NodeID subNodeId = *nodeIt;
        if (subNodeId != repNodeId)
        {
            mergeNodeToRep(subNodeId, repNodeId);
        }
    }
}

/**
 * Collapse node's points-to set. Change all points-to elements into field-insensitive.
 */
bool AndersenInc::collapseNodePts(NodeID nodeId)
{
    bool changed = false;
    const PointsTo& nodePts = getPts(nodeId);
    /// Points to set may be changed during collapse, so use a clone instead.
    PointsTo ptsClone = nodePts;
    for (PointsTo::iterator ptsIt = ptsClone.begin(), ptsEit = ptsClone.end(); ptsIt != ptsEit; ptsIt++)
    {
        if (isFieldInsensitive(*ptsIt))
            continue;

        if (collapseField(*ptsIt))
            changed = true;
    }
    return changed;
}

/**
 * Collapse field. make struct with the same base as nodeId become field-insensitive.
 */
bool AndersenInc::collapseField(NodeID nodeId)
{
    /// Black hole doesn't have structures, no collapse is needed.
    /// In later versions, instead of using base node to represent the struct,
    /// we'll create new field-insensitive node. To avoid creating a new "black hole"
    /// node, do not collapse field for black hole node.
    if (sCG->isBlkObjOrConstantObj(nodeId))
        return false;

    bool changed = false;

    double start = stat->getClk();

    // set base node field-insensitive.
    setObjFieldInsensitive(nodeId);

    // replace all occurrences of each field with the field-insensitive node
    NodeID baseId = sCG->getFIObjVar(nodeId);
    NodeID baseRepNodeId = sCG->sccRepNode(baseId);
    NodeBS & allFields = sCG->getAllFieldsObjVars(baseId);
    for (NodeBS::iterator fieldIt = allFields.begin(), fieldEit = allFields.end(); fieldIt != fieldEit; fieldIt++)
    {
        NodeID fieldId = *fieldIt;
        if (fieldId != baseId)
        {
            // use the reverse pts of this field node to find all pointers point to it
            const NodeSet revPts = getRevPts(fieldId);
            for (const NodeID o : revPts)
            {
                // change the points-to target from field to base node
                clearPts(o, fieldId);
                addPts(o, baseId);
                pushIntoWorklist(o);

                changed = true;
            }
            // merge field node into base node, including edges and pts.
            NodeID fieldRepNodeId = sCG->sccRepNode(fieldId);
            mergeNodeToRep(fieldRepNodeId, baseRepNodeId);
            if (fieldId != baseRepNodeId)
            {
                // gep node fieldId becomes redundant if it is merged to its base node who is set as field-insensitive
                // two node IDs should be different otherwise this field is actually the base and should not be removed.
                redundantGepNodes.set(fieldId);
            }
        }
    }

    if (sCG->isPWCNode(baseRepNodeId))
        if (collapseNodePts(baseRepNodeId))
            changed = true;

    double end = stat->getClk();
    timeOfCollapse += (end - start) / TIMEINTERVAL;

    return changed;
}

/*!
 * merge nodeId to newRepId. Return true if the newRepId is a PWC node
 */
bool AndersenInc::mergeSrcToTgt(NodeID nodeId, NodeID newRepId)
{

    if(nodeId==newRepId)
        return false;

    /// union pts of node to rep
    updatePropaPts(newRepId, nodeId);
    unionPts(newRepId,nodeId);

    /// move the edges from node to rep, and remove the node
    SConstraintNode* node = sCG->getSConstraintNode(nodeId);
    bool pwc = sCG->moveEdgesToRepNode(node, sCG->getSConstraintNode(newRepId));

    /// 1. if find gep edges inside SCC cycle, the rep node will become a PWC node and
    /// its pts should be collapsed later.
    /// 2. if the node to be merged is already a PWC node, the rep node will also become
    /// a PWC node as it will have a self-cycle gep edge.
    if(node->isPWCNode())
        pwc = true;

    /// set rep and sub relations
    updateNodeRepAndSubs(node->getId(),newRepId);

    sCG->removeSConstraintNode(node);

    return pwc;
}

/*
 * Merge a node to its rep node based on SCC detection
 */
void AndersenInc::mergeNodeToRep(NodeID nodeId,NodeID newRepId)
{

    if (mergeSrcToTgt(nodeId,newRepId))
        sCG->setPWCNode(newRepId);
}

/*
 * Updates subnodes of its rep, and rep node of its subs
 */
void AndersenInc::updateNodeRepAndSubs(NodeID nodeId, NodeID newRepId)
{
    sCG->setRep(nodeId,newRepId);
    NodeBS repSubs;
    repSubs.set(nodeId);
    /// update nodeToRepMap, for each subs of current node updates its rep to newRepId
    //  update nodeToSubsMap, union its subs with its rep Subs
    NodeBS& nodeSubs = sCG->sccSubNodes(nodeId);
    for(NodeBS::iterator sit = nodeSubs.begin(), esit = nodeSubs.end(); sit!=esit; ++sit)
    {
        NodeID subId = *sit;
        sCG->setRep(subId,newRepId);
    }
    repSubs |= nodeSubs;
    sCG->setSubs(newRepId,repSubs);
    sCG->resetSubs(nodeId);
}

/*!
 * SCC detection on constraint graph
 */
NodeStack& AndersenInc::SCCDetect()
{
    numOfSCCDetection++;

    double sccStart = stat->getClk();
    WPASConstraintSolver::SCCDetect();
    double sccEnd = stat->getClk();

    timeOfSCCDetection +=  (sccEnd - sccStart)/TIMEINTERVAL;

    double mergeStart = stat->getClk();

    mergeSccCycle();

    double mergeEnd = stat->getClk();

    timeOfSCCMerges +=  (mergeEnd - mergeStart)/TIMEINTERVAL;

    return getSCCDetector()->topoNodeStack();
}

/*!
 * Update call graph for the input indirect callsites
 */
bool AndersenInc::updateCallGraph(const CallSiteToFunPtrMap& callsites)
{

    double cgUpdateStart = stat->getClk();

    CallEdgeMap newEdges;
    onTheFlyCallGraphSolve(callsites,newEdges);
    NodePairSet cpySrcNodes;	/// nodes as a src of a generated new copy edge
    for(CallEdgeMap::iterator it = newEdges.begin(), eit = newEdges.end(); it!=eit; ++it )
    {
        CallSite cs = SVFUtil::getSVFCallSite(it->first->getCallSite());
        for(FunctionSet::iterator cit = it->second.begin(), ecit = it->second.end(); cit!=ecit; ++cit)
        {
            connectCaller2CalleeParams(cs,*cit,cpySrcNodes);
        }
    }
    for(NodePairSet::iterator it = cpySrcNodes.begin(), eit = cpySrcNodes.end(); it!=eit; ++it)
    {
        pushIntoWorklist(it->first);
    }

    double cgUpdateEnd = stat->getClk();
    timeOfUpdateCallGraph += (cgUpdateEnd - cgUpdateStart) / TIMEINTERVAL;

    return (!newEdges.empty());
}

void AndersenInc::heapAllocatorViaIndCall(CallSite cs, NodePairSet &cpySrcNodes)
{
    assert(SVFUtil::getCallee(cs) == nullptr && "not an indirect callsite?");
    RetICFGNode* retBlockNode = pag->getICFG()->getRetICFGNode(cs.getInstruction());
    const PAGNode* cs_return = pag->getCallSiteRet(retBlockNode);
    NodeID srcret;
    CallSite2DummyValPN::const_iterator it = callsite2DummyValPN.find(cs);
    if(it != callsite2DummyValPN.end())
    {
        // srcret = sccRepNode(it->second);
        srcret = it->second;
    }
    else
    {
        NodeID valNode = pag->addDummyValNode();
        NodeID objNode = pag->addDummyObjNode(cs.getType());
        addPts(valNode,objNode);
        callsite2DummyValPN.insert(std::make_pair(cs,valNode));
        fCG->addFConstraintNode(new FConstraintNode(valNode),valNode);
        fCG->addFConstraintNode(new FConstraintNode(objNode),objNode);
        sCG->addSConstraintNode(new SConstraintNode(valNode),valNode);
        sCG->addSConstraintNode(new SConstraintNode(objNode),objNode);
        srcret = valNode;
    }

    // NodeID dstrec = sccRepNode(cs_return->getId());
    NodeID dstrec = cs_return->getId();

    if(addCopyEdge(srcret, dstrec)) /// add copy sEdge with the original id. --wjy
        cpySrcNodes.insert(std::make_pair(srcret,dstrec));
}

/*!
 * Connect formal and actual parameters for indirect callsites
 */
void AndersenInc::connectCaller2CalleeParams(CallSite cs, const SVFFunction* F, NodePairSet &cpySrcNodes)
{
    assert(F);

    DBOUT(DAndersen, outs() << "connect parameters from indirect callsite " << cs.getInstruction()->toString() << " to callee " << *F << "\n");

    CallICFGNode* callBlockNode = pag->getICFG()->getCallICFGNode(cs.getInstruction());
    RetICFGNode* retBlockNode = pag->getICFG()->getRetICFGNode(cs.getInstruction());

    if(SVFUtil::isHeapAllocExtFunViaRet(F) && pag->callsiteHasRet(retBlockNode))
    {
        heapAllocatorViaIndCall(cs,cpySrcNodes);
    }

    if (pag->funHasRet(F) && pag->callsiteHasRet(retBlockNode))
    {
        const PAGNode* cs_return = pag->getCallSiteRet(retBlockNode);
        const PAGNode* fun_return = pag->getFunRet(F);
        if (cs_return->isPointer() && fun_return->isPointer())
        {
            // NodeID dstrec = sccRepNode(cs_return->getId());
            // NodeID srcret = sccRepNode(fun_return->getId());
            NodeID dstrec = cs_return->getId();
            NodeID srcret = fun_return->getId();
            if(addCopyEdge(srcret, dstrec)) /// add copy sEdge with the original id. --wjy
            {
                cpySrcNodes.insert(std::make_pair(srcret,dstrec));
            }
        }
        else
        {
            DBOUT(DAndersen, outs() << "not a pointer ignored\n");
        }
    }

    if (pag->hasCallSiteArgsMap(callBlockNode) && pag->hasFunArgsList(F))
    {

        // connect actual and formal param
        const SVFIR::SVFVarList& csArgList = pag->getCallSiteArgsList(callBlockNode);
        const SVFIR::SVFVarList& funArgList = pag->getFunArgsList(F);
        //Go through the fixed parameters.
        DBOUT(DPAGBuild, outs() << "      args:");
        SVFIR::SVFVarList::const_iterator funArgIt = funArgList.begin(), funArgEit = funArgList.end();
        SVFIR::SVFVarList::const_iterator csArgIt  = csArgList.begin(), csArgEit = csArgList.end();
        for (; funArgIt != funArgEit; ++csArgIt, ++funArgIt)
        {
            //Some programs (e.g. Linux kernel) leave unneeded parameters empty.
            if (csArgIt  == csArgEit)
            {
                DBOUT(DAndersen, outs() << " !! not enough args\n");
                break;
            }
            const PAGNode *cs_arg = *csArgIt ;
            const PAGNode *fun_arg = *funArgIt;

            if (cs_arg->isPointer() && fun_arg->isPointer())
            {
                DBOUT(DAndersen, outs() << "process actual parm  " << cs_arg->toString() << " \n");
                // NodeID srcAA = sccRepNode(cs_arg->getId());
                // NodeID dstFA = sccRepNode(fun_arg->getId());
                NodeID srcAA = cs_arg->getId();
                NodeID dstFA = fun_arg->getId();
                if(addCopyEdge(srcAA, dstFA)) /// add copy sEdge with the original id. --wjy
                {
                    cpySrcNodes.insert(std::make_pair(srcAA,dstFA));
                }
            }
        }

        //Any remaining actual args must be varargs.
        if (F->isVarArg())
        {
            // NodeID vaF = sccRepNode(pag->getVarargNode(F));
            NodeID vaF = pag->getVarargNode(F);
            DBOUT(DPAGBuild, outs() << "\n      varargs:");
            for (; csArgIt != csArgEit; ++csArgIt)
            {
                const PAGNode *cs_arg = *csArgIt;
                if (cs_arg->isPointer())
                {
                    // NodeID vnAA = sccRepNode(cs_arg->getId());
                    NodeID vnAA = cs_arg->getId();
                    if (addCopyEdge(vnAA,vaF)) /// add copy sEdge with the original id. --wjy
                    {
                        cpySrcNodes.insert(std::make_pair(vnAA,vaF));
                    }
                }
            }
        }
        if(csArgIt != csArgEit)
        {
            writeWrnMsg("too many args to non-vararg func.");
            writeWrnMsg("(" + cs.getInstruction()->getSourceLoc() + ")");
        }
    }
}


/*!
 * Print pag nodes' pts by an ascending order
 */
void AndersenInc::dumpTopLevelPtsTo()
{
    for (OrderedNodeSet::iterator nIter = this->getAllValidPtrs().begin();
            nIter != this->getAllValidPtrs().end(); ++nIter)
    {
        const PAGNode* node = getPAG()->getGNode(*nIter);
        if (getPAG()->isValidTopLevelPtr(node))
        {
            const PointsTo& pts = this->getPts(node->getId());
            outs() << "\nNodeID " << node->getId() << " ";

            if (pts.empty())
            {
                outs() << "\t\tPointsTo: {empty}\n\n";
            }
            else
            {
                outs() << "\t\tPointsTo: { ";

                multiset<u32_t> line;
                for (PointsTo::iterator it = pts.begin(), eit = pts.end();
                        it != eit; ++it)
                {
                    line.insert(*it);
                }
                for (multiset<u32_t>::const_iterator it = line.begin(); it != line.end(); ++it)
                    outs() << *it << " ";
                outs() << "}\n\n";
            }
        }
    }

    outs().flush();
}



/*!
 * solve worklist
 */
void AndersenInc::solveWorklist()
{
    // Initialize the nodeStack via a whole SCC detection
    // Nodes in nodeStack are in topological order by default.
    NodeStack& nodeStack = SCCDetect();

    // Process nodeStack and put the changed nodes into workList.
    while (!nodeStack.empty())
    {
        NodeID nodeId = nodeStack.top();
        nodeStack.pop();
        collapsePWCNode(nodeId);
        // process nodes in nodeStack
        processNode(nodeId);
        collapseFields();
    }

    // New nodes will be inserted into workList during processing.
    while (!isWorklistEmpty())
    {
        NodeID nodeId = popFromWorklist();
        // process nodes in worklist
        postProcessNode(nodeId);
    }
}

/*!
 * Process edge PAGNode
 */
void AndersenInc::processNode(NodeID nodeId)
{
    // This node may be merged during collapseNodePts() which means it is no longer a rep node
    // in the graph. Only rep node needs to be handled.
    if (sccRepNode(nodeId) != nodeId)
        return;

    double propStart = stat->getClk();
    SConstraintNode* node = sCG->getSConstraintNode(nodeId);
    handleCopyGep(node);
    double propEnd = stat->getClk();
    timeOfProcessCopyGep += (propEnd - propStart) / TIMEINTERVAL;
}

/*!
 * Post process node
 */
void AndersenInc::postProcessNode(NodeID nodeId)
{
    double insertStart = stat->getClk();

    SConstraintNode* node = sCG->getSConstraintNode(nodeId);

    // handle load
    for (SConstraintNode::const_iterator it = node->outgoingLoadsBegin(), eit = node->outgoingLoadsEnd();
            it != eit; ++it)
    {
        if (handleLoad(nodeId, *it))
            reanalyze = true;
    }
    // handle store
    for (SConstraintNode::const_iterator it = node->incomingStoresBegin(), eit =  node->incomingStoresEnd();
            it != eit; ++it)
    {
        if (handleStore(nodeId, *it))
            reanalyze = true;
    }

    double insertEnd = stat->getClk();
    timeOfProcessLoadStore += (insertEnd - insertStart) / TIMEINTERVAL;
}

/*!
 * Handle load
 */
bool AndersenInc::handleLoad(NodeID nodeId, const SConstraintEdge* edge)
{
    bool changed = false;
    for (PointsTo::iterator piter = getPts(nodeId).begin(), epiter = getPts(nodeId).end();
            piter != epiter; ++piter)
    {
        if (processLoad(*piter, edge))
        {
            changed = true;
        }
    }
    return changed;
}

/*!
 * Handle store
 */
bool AndersenInc::handleStore(NodeID nodeId, const SConstraintEdge* edge)
{
    bool changed = false;
    for (PointsTo::iterator piter = getPts(nodeId).begin(), epiter = getPts(nodeId).end();
            piter != epiter; ++piter)
    {
        if (processStore(*piter, edge))
        {
            changed = true;
        }
    }
    return changed;
}


bool AndersenInc::pushIntoDelEdgesWL(NodeID src, NodeID dst, FConstraintEdge::FConstraintEdgeK kind)
{
    FConstraintNode* srcNode = fCG->getFConstraintNode(src);
    FConstraintNode* dstNode = fCG->getFConstraintNode(dst);
    if (fCG->hasEdge(srcNode, dstNode, kind)) {
        FConstraintEdge* edge = fCG->getEdge(srcNode, dstNode, kind);
        delEdgesWL.push(edge);
        return true;
    }
    return false;
}

bool AndersenInc::pushIntoInsEdgesWL(NodeID src, NodeID dst, FConstraintEdge::FConstraintEdgeK kind)
{
    FConstraintNode* srcNode = fCG->getFConstraintNode(src);
    FConstraintNode* dstNode = fCG->getFConstraintNode(dst);
    if (fCG->hasEdge(srcNode, dstNode, kind)) {
        FConstraintEdge* edge = fCG->getEdge(srcNode, dstNode, kind);
        insEdgesWL.push(edge);
        return true;
    }
    return false;
}

/*
 * srcid --Load--> dstid
 * for o in pts(srcid):
 *     o --Copy--> dstid
 */
void AndersenInc::processLoadRemoval(NodeID srcid, NodeID dstid)
{
    SConstraintNode* sSrcNode = sCG->getSConstraintNode(srcid);
    SConstraintNode* sDstNode = sCG->getSConstraintNode(dstid);
    SConstraintEdge* sLoad = sCG->getEdge(sSrcNode, sDstNode, SConstraintEdge::SLoad);

    FConstraintNode* fSrcNode = fCG->getFConstraintNode(srcid);
    FConstraintNode* fDstNode = fCG->getFConstraintNode(dstid);
    FConstraintEdge* fLoad = fCG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FLoad);

    // 1. Process copy edge with this complex load constraint.
    const PointsTo& srcPts = getPts(srcid);
    for (NodeID o: srcPts) {
        if (pag->isConstantObj(o) || isNonPointerObj(o))
            continue;
        FConstraintNode* fONode = fCG->getFConstraintNode(o);
        FConstraintEdge* fEdge = fCG->getEdge(fONode, fDstNode, FConstraintEdge::FCopy);
        CopyFCGEdge* fCopy = SVFUtil::dyn_cast<CopyFCGEdge>(fEdge);
        fCopy->removeComplexEdge(fLoad);
        if (fCopy->getComplexEdgeSet().empty()) {
            // fCopy need to be removed
            pushIntoDelEdgesWL(o, dstid, FConstraintEdge::FCopy);
        }
    }

    // 2. Process fedge set of the sedge which this fedge retargeted to.
    sLoad->removeFEdge(fLoad);
    if (sLoad->getFEdgeSet().empty()) {
        sCG->removeLoadEdge(SVFUtil::dyn_cast<LoadSCGEdge>(sLoad));
    }

    // 3. process fedges removal
    fCG->removeLoadEdge(SVFUtil::dyn_cast<LoadFCGEdge>(fLoad));
}

/*
 * srcid --Store--> dstid
 * for o in pts(dstid):
 *     srcid --Copy--> o
 */
void AndersenInc::processStoreRemoval(NodeID srcid, NodeID dstid)
{
    SConstraintNode* sSrcNode = sCG->getSConstraintNode(srcid);
    SConstraintNode* sDstNode = sCG->getSConstraintNode(dstid);
    SConstraintEdge* sStore = sCG->getEdge(sSrcNode, sDstNode, SConstraintEdge::SStore);

    FConstraintNode* fSrcNode = fCG->getFConstraintNode(srcid);
    FConstraintNode* fDstNode = fCG->getFConstraintNode(dstid);
    FConstraintEdge* fStore = fCG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FStore);

    const PointsTo& dstPts = getPts(dstid);

    for (NodeID o: dstPts) {
        if (pag->isConstantObj(o) || isNonPointerObj(o))
            continue;
        FConstraintNode* fONode = fCG->getFConstraintNode(o);
        FConstraintEdge* fEdge = fCG->getEdge(fSrcNode, fONode, FConstraintEdge::FCopy);
        CopyFCGEdge* fCopy = SVFUtil::dyn_cast<CopyFCGEdge>(fEdge);
        fCopy->removeComplexEdge(fStore);
        if (fCopy->getComplexEdgeSet().empty()) {
            // fCopy need to be removed
            pushIntoDelEdgesWL(srcid, o, FConstraintEdge::FCopy);
        }
    }

    sStore->removeFEdge(fStore);
    if (sStore->getFEdgeSet().empty()) {
        sCG->removeStoreEdge(SVFUtil::dyn_cast<StoreSCGEdge>(sStore));
    }

    fCG->removeStoreEdge(SVFUtil::dyn_cast<StoreFCGEdge>(fStore));
}

/*
 * s --Addr--> d
 * pts(d) = pts(d) \Union {s}
 */
void AndersenInc::processAddrRemoval(NodeID srcid, NodeID dstid)
{
    SConstraintNode* sSrcNode = sCG->getSConstraintNode(srcid);
    SConstraintNode* sDstNode = sCG->getSConstraintNode(dstid);
    SConstraintEdge* sAddr = sCG->getEdge(sSrcNode, sDstNode, SConstraintEdge::SAddr);

    FConstraintNode* fSrcNode = fCG->getFConstraintNode(srcid);
    FConstraintNode* fDstNode = fCG->getFConstraintNode(dstid);
    FConstraintEdge* fAddr = fCG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FAddr);

    sAddr->removeFEdge(fAddr);
    if (sAddr->getFEdgeSet().empty()) {
        sCG->removeAddrEdge(SVFUtil::dyn_cast<AddrSCGEdge>(sAddr));
    }
    
    fCG->removeAddrEdge(SVFUtil::dyn_cast<AddrFCGEdge>(fAddr));

    PointsTo srcSet;
    srcSet.set(srcid);
    propagateDelPts(srcSet, dstid);
}

/*
 * s --Copy--> d
 * pts(d) = pts(d) \Union pts(s)
 */
void AndersenInc::processCopyRemoval(NodeID srcid, NodeID dstid)
{
    // process original copy first
    FConstraintNode* fSrcNode = fCG->getFConstraintNode(srcid);
    FConstraintNode* fDstNode = fCG->getFConstraintNode(dstid);
    FConstraintEdge* fCopy = fCG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FCopy);
    CopyFCGEdge* copyFCGEdge = SVFUtil::dyn_cast<CopyFCGEdge>(fCopy);
    if (! copyFCGEdge->getComplexEdgeSet().empty()) {
        // not empty, original copy removal (remove self complex constraint)
        copyFCGEdge->removeComplexEdge(fCopy);
        if (! copyFCGEdge->getComplexEdgeSet().empty())
            return; // do nothing if the complex set is still not empty
    }

    SConstraintNode* sSrcNode = sCG->getSConstraintNode(srcid);
    SConstraintNode* sDstNode = sCG->getSConstraintNode(dstid);
    if (sSrcNode == sDstNode) {
        // Copy Edge in SCC
        NodeBS newReps;
        NodeID oldRep;
        unsigned sccKeep = sCG->sccBreakDetect(srcid, dstid, FConstraintEdge::FCopy, newReps, oldRep);
        if (1 == sccKeep) {
            // SCC KEEP
            // SCC KEEP should remove the fEdge
            return;
        }
        // SCC Restore
        // SCC Restore should remove the fEdge and sEdge
        // reset Pts for new rep nodes
        for (NodeID id: newReps) {
            unionPts(id, getPts(oldRep));
        }
        propagateDelPts(getPts(srcid), dstid);
    }
    else {
        SConstraintEdge* sCopy = sCG->getEdge(sSrcNode, sDstNode, SConstraintEdge::SCopy);
        // 
        sCopy->removeFEdge(fCopy);
        if (sCopy->getFEdgeSet().empty()) {
            sCG->removeDirectEdge(sCopy);
            propagateDelPts(getPts(sSrcNode->getId()), sDstNode->getId());
        }

        fCG->removeDirectEdge(fCopy);
    }
}

/*
 * s --VGep--> d
 * pts(d) = pts(d) \Union FI(pts(s))
 */
void AndersenInc::processVariantGepRemoval(NodeID srcid, NodeID dstid)
{
    SConstraintNode* sSrcNode = sCG->getSConstraintNode(srcid);
    SConstraintNode* sDstNode = sCG->getSConstraintNode(dstid);
    PointsTo tmpDstPts;
    if (sSrcNode == sDstNode) {
        // VGep Edge in SCC
        NodeBS newReps;
        NodeID oldRep;
        unsigned sccKeep = sCG->sccBreakDetect(srcid, dstid, FConstraintEdge::FVariantGep, newReps, oldRep);
        if (1 == sccKeep) {
            // SCC KEEP
            // SCC KEEP should remove the fEdge
            return;
        }
        // SCC Restore
        // SCC Restore should remove the fEdge and sEdge
        // reset Pts for new rep nodes
        for (NodeID id: newReps) {
            unionPts(id, getPts(oldRep));
        }
        // SCC Restore
        // SCC Restore should remove the fEdge and sEdge

        // VGep Constraint
        for (NodeID o: getPts(srcid)) {
            if (sCG->isBlkObjOrConstantObj(o))
            {
                tmpDstPts.set(o);
                continue;
            }

            // if (!isFieldInsensitive(o))
            // {
            //     setObjFieldInsensitive(o);
            //     sCG->addNodeToBeCollapsed(sCG->getBaseObjVar(o));
            // }

            // Add the field-insensitive node into pts.
            NodeID baseId = sCG->getFIObjVar(o);
            tmpDstPts.set(baseId);
        }
        propagateDelPts(tmpDstPts, dstid);
    }
    else {
        SConstraintEdge* sVGep = sCG->getEdge(sSrcNode, sDstNode, SConstraintEdge::SVariantGep);
        FConstraintNode* fSrcNode = fCG->getFConstraintNode(srcid);
        FConstraintNode* fDstNode = fCG->getFConstraintNode(dstid);
        FConstraintEdge* fVGep = fCG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FVariantGep);

        // 
        sVGep->removeFEdge(fVGep);
        if (sVGep->getFEdgeSet().empty()) {
            sCG->removeDirectEdge(sVGep);
            // VGep Constraint
            for (NodeID o: getPts(sSrcNode->getId())) {
                if (sCG->isBlkObjOrConstantObj(o))
                {
                    tmpDstPts.set(o);
                    continue;
                }
                // About isFieldInsensitive?
                // Add the field-insensitive node into pts.
                NodeID baseId = sCG->getFIObjVar(o);
                tmpDstPts.set(baseId);
            }
            propagateDelPts(tmpDstPts, sDstNode->getId());
        }

        fCG->removeDirectEdge(fVGep);
    }
}

/*
 * s --NGep: ap--> d
 * pts(d) = pts(d) \Union AP(pts(s))
 */
void AndersenInc::processNormalGepRemoval(NodeID srcid, NodeID dstid, const AccessPath& ap)
{
    SConstraintNode* sSrcNode = sCG->getSConstraintNode(srcid);
    SConstraintNode* sDstNode = sCG->getSConstraintNode(dstid);
    PointsTo tmpDstPts;
    if (sSrcNode == sDstNode) {
        // NGep Edge in SCC
        NodeBS newReps;
        NodeID oldRep;
        unsigned sccKeep = sCG->sccBreakDetect(srcid, dstid, FConstraintEdge::FNormalGep, newReps, oldRep);
        if (1 == sccKeep) {
            // SCC KEEP
            // SCC KEEP should remove the fEdge
            return;
        }
        // SCC Restore
        // SCC Restore should remove the fEdge and sEdge
        // reset Pts for new rep nodes
        for (NodeID id: newReps) {
            unionPts(id, getPts(oldRep));
        }

        // SCC Restore
        // SCC Restore should remove the fEdge and sEdge

        // NGep Constraint
        for (NodeID o : getPts(srcid))
        {
            if (sCG->isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
            {
                tmpDstPts.set(o);
                continue;
            }
            NodeID fieldSrcPtdNode = sCG->getGepObjVar(o, ap.getConstantFieldIdx());
            tmpDstPts.set(fieldSrcPtdNode);
        }

        propagateDelPts(tmpDstPts, dstid);
    }
    else {
        SConstraintEdge* sNGep = sCG->getEdge(sSrcNode, sDstNode, SConstraintEdge::SNormalGep);
        FConstraintNode* fSrcNode = fCG->getFConstraintNode(srcid);
        FConstraintNode* fDstNode = fCG->getFConstraintNode(dstid);
        FConstraintEdge* fNGep = fCG->getEdge(fSrcNode, fDstNode, FConstraintEdge::FNormalGep);

        // 
        sNGep->removeFEdge(fNGep);
        if (sNGep->getFEdgeSet().empty()) {
            sCG->removeDirectEdge(sNGep);
            // NGep Constraint
            for (NodeID o : getPts(sSrcNode->getId()))
            {
                if (sCG->isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
                {
                    tmpDstPts.set(o);
                    continue;
                }
                NodeID fieldSrcPtdNode = sCG->getGepObjVar(o, ap.getConstantFieldIdx());
                tmpDstPts.set(fieldSrcPtdNode);
            }

            propagateDelPts(tmpDstPts, sDstNode->getId());
        }

        fCG->removeDirectEdge(fNGep);
    }
}

// TODO: --wjy
void AndersenInc::propagateDelPts(const PointsTo& pts, NodeID nodeId)
{
    if (pts.empty())
        return;
    
    SConstraintNode* node = sCG->getSConstraintNode(nodeId);
    PointsTo dPts; // objs need to be removed from pts(nodeId)
    dPts |= pts;

    // Filter 1: dPts = dPts \intersect pts(nodeId)
    const PointsTo& nodePts = getPts(nodeId);
    dPts &= nodePts;
    
    // Filter 2: incoming neighbors check
    for (auto it = node->directInEdgeBegin(), eit = node->directInEdgeEnd();
        it != eit; ++it)
    {
        if (dPts.empty()) {
            return;
        }

        const SConstraintEdge* incomingEdge = *it;
        NodeID src = incomingEdge->getSrcID();
        const PointsTo & srcPts = getPts(src);

        if (SVFUtil::isa<CopySCGEdge>(incomingEdge)) {
            dPts -= srcPts;
        }
        else if (SVFUtil::isa<VariantGepSCGEdge>(incomingEdge)) {
            for (NodeID o: srcPts) {
                if (sCG->isBlkObjOrConstantObj(o))
                    dPts.reset(o);
                else 
                    dPts.reset(sCG->getFIObjVar(o));
            }
        }
        else if (SVFUtil::isa<NormalGepSCGEdge>(incomingEdge)) {
            const NormalGepSCGEdge* ngep = SVFUtil::dyn_cast<NormalGepSCGEdge>(incomingEdge);
            for (NodeID o: srcPts) {
                if (sCG->isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
                    dPts.reset(o);
                else {
                    const AccessPath& ap = ngep->getAccessPath();
                    NodeID fieldSrcPtdNode = sCG->getGepObjVar(o, ap.getConstantFieldIdx());
                    dPts.reset(fieldSrcPtdNode);
                }
            }
        }
    }

    // pts(nodeId) = pts(nodeId) - dPts
    for (NodeID o: dPts) {
        clearPts(nodeId, o);
    }

    // process outgoing neighbor propagate
    for (auto it = node->directOutEdgeBegin(), eit = node->directOutEdgeEnd();
        it != eit; ++it)
    {
        const SConstraintEdge* outSEdge = *it;
        NodeID dstId = outSEdge->getDstID();
        if (dstId == nodeId)
            continue; // self circle edge
        if (SVFUtil::isa<CopySCGEdge>(outSEdge)) {
            propagateDelPts(dPts, dstId);
        }
        else if (SVFUtil::isa<VariantGepSCGEdge>(outSEdge)) {
            PointsTo vgepProPts;
            for (NodeID o: dPts) {
                if (sCG->isBlkObjOrConstantObj(o))
                    vgepProPts.set(o);
                else
                    vgepProPts.set(sCG->getFIObjVar(o));
            }
            propagateDelPts(vgepProPts, dstId);
        }
        else if (SVFUtil::isa<NormalGepSCGEdge>(outSEdge)) {
            const NormalGepSCGEdge* ngep = SVFUtil::dyn_cast<NormalGepSCGEdge>(outSEdge);
            PointsTo ngepProPts;
            for (NodeID o: dPts) {
                if (sCG->isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
                    ngepProPts.set(o);
                else {
                    const AccessPath& ap = ngep->getAccessPath();
                    NodeID fieldSrcPtdNode = sCG->getGepObjVar(o, ap.getConstantFieldIdx());
                    ngepProPts.set(fieldSrcPtdNode);
                }
            }
            propagateDelPts(ngepProPts, dstId);
        }
    }

    // process complex constraint 
    for (NodeID o: dPts) {
        if (pag->isConstantObj(o) || isNonPointerObj(o))
            continue;

        FConstraintNode* oNode = fCG->getFConstraintNode(o);

        // load complex constraint
        for (auto it = node->outgoingLoadsBegin(), eit = node->outgoingLoadsEnd();
            it != eit; ++it)
        {
            const SConstraintEdge* sLoad = *it;
            for (FConstraintEdge* fLoad: sLoad->getFEdgeSet()) 
            {
                FConstraintNode* loadDstNode = fLoad->getDstNode();
                FConstraintEdge* fEdge = fCG->getEdge(oNode, loadDstNode, FConstraintEdge::FCopy);
                CopyFCGEdge* fCopy = SVFUtil::dyn_cast<CopyFCGEdge>(fEdge);
                fCopy->removeComplexEdge(fLoad);
                if (fCopy->getComplexEdgeSet().empty())
                    pushIntoDelEdgesWL(o, fLoad->getDstID(), FConstraintEdge::FCopy);
            }
        }

        // store complex constraint
        for (auto it = node->incomingStoresBegin(), eit = node->incomingStoresEnd();
            it != eit; ++it)
        {
            const SConstraintEdge* sStore = *it;
            for (FConstraintEdge* fStore: sStore->getFEdgeSet()) 
            {
                FConstraintNode* storeSrcNode = fStore->getSrcNode();
                FConstraintEdge* fEdge = fCG->getEdge(storeSrcNode, oNode, FConstraintEdge::FCopy);
                CopyFCGEdge* fCopy = SVFUtil::dyn_cast<CopyFCGEdge>(fEdge);
                fCopy->removeComplexEdge(fStore);
                if (fCopy->getComplexEdgeSet().empty())
                    pushIntoDelEdgesWL(fStore->getSrcID(), o, FConstraintEdge::FCopy);
            }
        }
    }
}

void AndersenInc::processDeletion()
{
    // pushIntoDelEdgesWL(47, 61, FConstraintEdge::FLoad);
    bool newCallCopyEdge = false;
    do {
        newCallCopyEdge = false;
        while (!delEdgesWL.empty()) {
            FConstraintEdge* fEdge = delEdgesWL.pop();
            NodeID src = fEdge->getSrcID();
            NodeID dst = fEdge->getDstID();
            if (SVFUtil::isa<AddrFCGEdge>(fEdge)) {
                processAddrRemoval(src, dst);
            }
            else if (SVFUtil::isa<CopyFCGEdge>(fEdge)) {
                processCopyRemoval(src, dst);
            }
            else if (SVFUtil::isa<VariantGepFCGEdge>(fEdge)) {
                processVariantGepRemoval(src, dst);
            }
            else if (SVFUtil::isa<NormalGepFCGEdge>(fEdge)) {
                NormalGepFCGEdge* ngep = SVFUtil::dyn_cast<NormalGepFCGEdge>(fEdge);
                const AccessPath& ap = ngep->getAccessPath();
                processNormalGepRemoval(src, dst, ap);
            }
            else if (SVFUtil::isa<StoreFCGEdge>(fEdge)) {
                processStoreRemoval(src, dst);
            }
            else if (SVFUtil::isa<LoadFCGEdge>(fEdge)) {
                processLoadRemoval(src, dst);
            }
        }
        // computeFpPDM(); todo
        // if (updateCallGraphDel(getIndirectCallsites()))
        //     newCallCopyEdge = true;

    } while (newCallCopyEdge);
}


void AndersenInc::initFpPDM() {
    fpPtsDiffMap.clear();
    const CallSiteToFunPtrMap& callsites = getIndirectCallsites();
    for(CallSiteToFunPtrMap::const_iterator iter = callsites.begin(), eiter = callsites.end(); 
        iter != eiter; ++iter)
    {
        const CallICFGNode* cs = iter->first;

        if (SVFUtil::getSVFCallSite(cs->getCallSite()).isVirtualCall())
        {
            const SVFValue *vtbl = SVFUtil::getSVFCallSite(cs->getCallSite()).getVtablePtr();
            assert(pag->hasValueNode(vtbl));
            NodeID vtblId = pag->getValueNode(vtbl);

            PtsDiff* pd = new PtsDiff;
            pd->nodeId = vtblId;
            pd->prePts = getPts(vtblId);
            pd->nowPts = getPts(vtblId);
            fpPtsDiffMap[vtblId] = pd;
        }
        else
        {
            PtsDiff* pd = new PtsDiff;
            pd->nodeId = iter->second;
            pd->prePts = getPts(iter->second);
            pd->nowPts = getPts(iter->second);
            fpPtsDiffMap[iter->second] = pd;
        }
    }
}

void AndersenInc::computeFpPDM() {
    for(auto iter = fpPtsDiffMap.begin(), eiter = fpPtsDiffMap.end(); 
        iter != eiter; ++iter)
    {
        NodeID nodeid = iter->first;
        PtsDiff* pd = iter->second;
        PointsTo ptspre = pd->nowPts;
        PointsTo ptsnow = getPts(nodeid);
        pd->insPts.clear();
        pd->delPts.clear();
        pd->insPts |= (ptsnow - ptspre);
        pd->delPts |= (ptspre - ptsnow);
        pd->prePts.clear();
        pd->prePts |= ptspre;
        pd->nowPts.clear();
        pd->nowPts |= ptsnow;
    }
}

bool AndersenInc::updateCallGraphDel(const CallSiteToFunPtrMap& callsites)
{

    double cgUpdateStart = stat->getClk();

    CallEdgeMap newEdges;
    onTheFlyCallGraphSolveDel(callsites,newEdges);
    NodePairSet cpySrcNodes;	/// nodes as a src of a generated new copy edge
    for(CallEdgeMap::iterator it = newEdges.begin(), eit = newEdges.end(); it!=eit; ++it )
    {
        CallSite cs = SVFUtil::getSVFCallSite(it->first->getCallSite());
        for(FunctionSet::iterator cit = it->second.begin(), ecit = it->second.end(); cit!=ecit; ++cit)
        {
            connectCaller2CalleeParamsDel(cs,*cit,cpySrcNodes);
        }
    }
    // for(NodePairSet::iterator it = cpySrcNodes.begin(), eit = cpySrcNodes.end(); it!=eit; ++it)
    // {
    //     pushIntoWorklist(it->first);
    // }

    double cgUpdateEnd = stat->getClk();
    // timeOfUpdateCallGraph += (cgUpdateEnd - cgUpdateStart) / TIMEINTERVAL;
    timeOfUpdateCallGraph += (cgUpdateEnd - cgUpdateStart);

    return (!newEdges.empty());
}

void AndersenInc::onTheFlyCallGraphSolveDel(const CallSiteToFunPtrMap& callsites, CallEdgeMap& newEdges)
{
    for(CallSiteToFunPtrMap::const_iterator iter = callsites.begin(), eiter = callsites.end(); 
        iter != eiter; ++iter)
    {
        const CallICFGNode* cs = iter->first;

        if (SVFUtil::getSVFCallSite(cs->getCallSite()).isVirtualCall())
        {
            const SVFValue *vtbl = SVFUtil::getSVFCallSite(cs->getCallSite()).getVtablePtr();
            assert(pag->hasValueNode(vtbl));
            NodeID vtblId = pag->getValueNode(vtbl);
            PtsDiff* pd = fpPtsDiffMap[vtblId];
            if (pd->delPts.empty())
                continue;   // if no pts changed, then do nothing
            // resolveCPPIndCallsDel(cs, getPts(vtblId), newEdges);
            const PointsTo & delPts = pd->delPts;
            resolveCPPIndCallsDel(cs, delPts, newEdges);
        }
        else {
            PtsDiff* pd = fpPtsDiffMap[iter->second];
            if (pd->delPts.empty())
                continue;   // if no pts changed, then do nothing
            const PointsTo & delPts = pd->delPts;
            // resolveIndCallsDel(iter->first,getPts(iter->second),newEdges);
            resolveIndCallsDel(iter->first, delPts, newEdges);
        }
    }
}

// TODO
void AndersenInc::resolveCPPIndCallsDel(const CallICFGNode* cs, const PointsTo& target, CallEdgeMap& newEdges)
{
    assert(SVFUtil::getSVFCallSite(cs->getCallSite()).isVirtualCall() && "not cpp virtual call");

    VFunSet vfns;
    if (Options::ConnectVCallOnCHA())
        getVFnsFromCHA(cs, vfns);
    else
        getVFnsFromPts(cs, target, vfns);
    connectVCallToVFnsDel(cs, vfns, newEdges); // TODO: handle indirect call edge?
}

void AndersenInc::resolveIndCallsDel(const CallICFGNode* cs, const PointsTo& target, CallEdgeMap& newEdges)
 {
    assert(pag->isIndirectCallSites(cs) && "not an indirect callsite?");
    /// discover indirect pointer target
     for (PointsTo::iterator ii = target.begin(), ie = target.end();
            ii != ie; ii++)
    {

        if(getNumOfResolvedIndCallEdge() >= Options::IndirectCallLimit())
        {
            wrnMsg("Resolved Indirect Call Edges are Out-Of-Budget, please increase the limit");
            return;
        }

        if(ObjVar* objPN = SVFUtil::dyn_cast<ObjVar>(pag->getGNode(*ii)))
        {
            const MemObj* obj = pag->getObject(objPN);

            if(obj->isFunction())
            {
                const SVFFunction* calleefun = SVFUtil::cast<SVFFunction>(obj->getValue());
                const SVFFunction* callee = calleefun->getDefFunForMultipleModule();

                /// if the arg size does not match then we do not need to connect this parameter
                /// even if the callee is a variadic function (the first parameter of variadic function is its paramter number)
                if(SVFUtil::matchArgs(cs->getCallSite(), callee) == false)
                    continue;

                // if(0 == getIndCallMap()[cs].count(callee))
                // {
                //     newEdges[cs].insert(callee);
                //     getIndCallMap()[cs].insert(callee);

                //     ptaCallGraph->addIndirectCallGraphEdge(cs, cs->getCaller(), callee);
                //     // FIXME: do we need to update llvm call graph here?
                //     // The indirect call is maintained by ourself, We may update llvm's when we need to
                //     //CallGraphNode* callgraphNode = callgraph->getOrInsertFunction(cs.getCaller());
                //     //callgraphNode->addCalledFunction(cs,callgraph->getOrInsertFunction(callee));
                // }
                if(0 < getIndCallMap()[cs].count(callee))
                {
                    newEdges[cs].insert(callee);
                    getIndCallMap()[cs].erase(callee);

                    ptaCallGraph->removeIndirectCallGraphEdge(cs, cs->getCaller(), callee);
                }
            }
        }
    }   
 }

 void AndersenInc::connectVCallToVFnsDel(const CallICFGNode* cs, const VFunSet &vfns, CallEdgeMap& newEdges)
{
    //// connect all valid functions
    for (VFunSet::const_iterator fit = vfns.begin(),
            feit = vfns.end(); fit != feit; ++fit)
    {
        const SVFFunction* callee = *fit;
        callee = callee->getDefFunForMultipleModule();
        // if (getIndCallMap()[cs].count(callee) > 0)
        //     continue;
        if (getIndCallMap()[cs].count(callee) == 0)
            continue;
        if(SVFUtil::getSVFCallSite(cs->getCallSite()).arg_size() == callee->arg_size() ||
                (SVFUtil::getSVFCallSite(cs->getCallSite()).isVarArg() && callee->isVarArg()))
        {
            newEdges[cs].insert(callee);
            getIndCallMap()[cs].erase(callee);
            const CallICFGNode* callBlockNode = pag->getICFG()->getCallICFGNode(cs->getCallSite());
            ptaCallGraph->removeIndirectCallGraphEdge(callBlockNode, cs->getCaller(),callee);
        }
    }
}

void AndersenInc::connectCaller2CalleeParamsDel(CallSite cs, const SVFFunction* F, NodePairSet &cpySrcNodes)
{
    assert(F);

    DBOUT(DAndersen, SVFUtil::outs() << "connect parameters from indirect callsite " << *cs.getInstruction() << " to callee " << *F << "\n");

    CallICFGNode* callBlockNode = pag->getICFG()->getCallICFGNode(cs.getInstruction());
    RetICFGNode* retBlockNode = pag->getICFG()->getRetICFGNode(cs.getInstruction());

    if(SVFUtil::isHeapAllocExtFunViaRet(F) && pag->callsiteHasRet(retBlockNode))
    {
        // heapAllocatorViaIndCall(cs,cpySrcNodes); // TODO 
        SVFUtil::outs() << "Do not handle heapAllocatorViaIndCall in incremental analysis!\n";
    }

    if (pag->funHasRet(F) && pag->callsiteHasRet(retBlockNode))
    {
        const PAGNode* cs_return = pag->getCallSiteRet(retBlockNode);
        const PAGNode* fun_return = pag->getFunRet(F);
        if (cs_return->isPointer() && fun_return->isPointer())
        {
            NodeID dstrec = cs_return->getId();
            NodeID srcret = fun_return->getId();
            // if(addCopyEdge(srcret, dstrec)) // TODO: ret-->rec
            // {
            //     cpySrcNodes.insert(std::make_pair(srcret,dstrec));
            // }
            pushIntoDelEdgesWL(srcret, dstrec, FConstraintEdge::FCopy);
        }
        else
        {
            DBOUT(DAndersen, SVFUtil::outs() << "not a pointer ignored\n");
        }
    }

    if (pag->hasCallSiteArgsMap(callBlockNode) && pag->hasFunArgsList(F))
    {

        // connect actual and formal param
        const SVFIR::SVFVarList& csArgList = pag->getCallSiteArgsList(callBlockNode);
        const SVFIR::SVFVarList& funArgList = pag->getFunArgsList(F);
        //Go through the fixed parameters.
        DBOUT(DPAGBuild, outs() << "      args:");
        SVFIR::SVFVarList::const_iterator funArgIt = funArgList.begin(), funArgEit = funArgList.end();
        SVFIR::SVFVarList::const_iterator csArgIt  = csArgList.begin(), csArgEit = csArgList.end();
        for (; funArgIt != funArgEit; ++csArgIt, ++funArgIt)
        {
            //Some programs (e.g. Linux kernel) leave unneeded parameters empty.
            if (csArgIt  == csArgEit)
            {
                DBOUT(DAndersen, SVFUtil::outs() << " !! not enough args\n");
                break;
            }
            const PAGNode *cs_arg = *csArgIt ;
            const PAGNode *fun_arg = *funArgIt;

            if (cs_arg->isPointer() && fun_arg->isPointer())
            {
                DBOUT(DAndersen, SVFUtil::outs() << "process actual parm  " << cs_arg->toString() << " \n");
                NodeID srcAA = cs_arg->getId();
                NodeID dstFA = fun_arg->getId();
                // if(addCopyEdge(srcAA, dstFA)) // TODO: act arg --> fom arg
                // {
                //     cpySrcNodes.insert(std::make_pair(srcAA,dstFA));
                // }
                pushIntoDelEdgesWL(srcAA, dstFA, FConstraintEdge::FCopy);
            }
        }

        //Any remaining actual args must be varargs.
        if (F->isVarArg())
        {
            NodeID vaF = pag->getVarargNode(F);
            DBOUT(DPAGBuild, SVFUtil::outs() << "\n      varargs:");
            for (; csArgIt != csArgEit; ++csArgIt)
            {
                const PAGNode *cs_arg = *csArgIt;
                if (cs_arg->isPointer())
                {
                    NodeID vnAA = cs_arg->getId();
                    // if (addCopyEdge(vnAA,vaF)) // TODO: remaining actual arg --> var arg
                    // {
                    //     cpySrcNodes.insert(std::make_pair(vnAA,vaF));
                    // }
                    pushIntoDelEdgesWL(vnAA, vaF, FConstraintEdge::FCopy);
                }
            }
        }
        if(csArgIt != csArgEit)
        {
            writeWrnMsg("too many args to non-vararg func.");
            writeWrnMsg("(" + cs.getInstruction()->getSourceLoc() + ")");
        }
    }
}
