
#ifndef SUPERCONSG_H_
#define SUPERCONSG_H_

#include "Graphs/SuperConsGEdge.h"
#include "Graphs/SuperConsGNode.h"
#include "Graphs/FlatConsG.h"
#include "Graphs/ConsG.h"
#include "Util/SCC.h"

namespace SVF
{

class SConstraintGraph : public GenericGraph<SConstraintNode, SConstraintEdge>
{

public:
    typedef OrderedMap<NodeID, SConstraintNode *> SConstraintNodeIDToNodeMapTy;
    typedef SConstraintEdge::SConstraintEdgeSetTy::iterator SConstraintNodeIter;
    typedef Map<NodeID, NodeID> NodeToRepMap;
    typedef Map<NodeID, NodeBS> NodeToSubsMap;
    typedef FIFOWorkList<NodeID> WorkList;

protected:
    SVFIR* pag;
    NodeToRepMap nodeToRepMap;
    NodeToSubsMap nodeToSubsMap;
    WorkList nodesToBeCollapsed;
    EdgeID edgeIndex;
    FConstraintGraph* fConsG;
    SConstraintEdge::SConstraintEdgeSetTy AddrSCGEdgeSet;
    SConstraintEdge::SConstraintEdgeSetTy directSEdgeSet;
    SConstraintEdge::SConstraintEdgeSetTy LoadSCGEdgeSet;
    SConstraintEdge::SConstraintEdgeSetTy StoreSCGEdgeSet;

    inline SConstraintEdge::SConstraintEdgeK F2SKind(FConstraintEdge::FConstraintEdgeK fkind)
    {
        switch (fkind)
        {
        case FConstraintEdge::FAddr:
            return SConstraintEdge::SAddr;
        case FConstraintEdge::FCopy:
            return SConstraintEdge::SCopy;
        case FConstraintEdge::FStore:
            return SConstraintEdge::SStore;
        case FConstraintEdge::FLoad:
            return SConstraintEdge::SLoad;
        case FConstraintEdge::FVariantGep:
            return SConstraintEdge::SVariantGep;
        default:
            return SConstraintEdge::SNormalGep;
        }
    }

    void buildSCG();

    void destroy();

    SVFStmt::SVFStmtSetTy& getPAGEdgeSet(SVFStmt::PEDGEK kind)
    {
        return pag->getPTASVFStmtSet(kind);
    }

    /// Wappers used internally, not expose to Andernsen Pass
    //@{
    inline NodeID getValueNode(const SVFValue* value) const
    {
        return sccRepNode(pag->getValueNode(value));
    }

    inline NodeID getReturnNode(const SVFFunction* value) const
    {
        return pag->getReturnNode(value);
    }

    inline NodeID getVarargNode(const SVFFunction* value) const
    {
        return pag->getVarargNode(value);
    }
    //@}

public:
    /// Constructor
    SConstraintGraph(SVFIR* p, FConstraintGraph* fCG): pag(p), edgeIndex(0), fConsG(fCG)
    {
        buildSCG();
    }
    /// Destructor
    virtual ~SConstraintGraph()
    {
        destroy();
    }

    /// Get/add/remove constraint node
    //@{
    inline SConstraintNode* getSConstraintNode(NodeID id) const
    {
        id = sccRepNode(id);
        return getGNode(id);
    }
    inline void addSConstraintNode(SConstraintNode* node, NodeID id)
    {
        addGNode(id,node);
    }
    inline bool hasSConstraintNode(NodeID id) const
    {
        id = sccRepNode(id);
        return hasGNode(id);
    }
    inline void removeSConstraintNode(SConstraintNode* node)
    {
        removeGNode(node);
    }
    //@}

    //// Return true if this edge exits
    inline bool hasEdge(SConstraintNode* src, SConstraintNode* dst, SConstraintEdge::SConstraintEdgeK kind)
    {
        SConstraintEdge edge(src,dst,kind);
        if(kind == SConstraintEdge::SCopy ||
                kind == SConstraintEdge::SNormalGep || kind == SConstraintEdge::SVariantGep)
            return directSEdgeSet.find(&edge) != directSEdgeSet.end();
        else if(kind == SConstraintEdge::SAddr)
            return AddrSCGEdgeSet.find(&edge) != AddrSCGEdgeSet.end();
        else if(kind == SConstraintEdge::SStore)
            return StoreSCGEdgeSet.find(&edge) != StoreSCGEdgeSet.end();
        else if(kind == SConstraintEdge::SLoad)
            return LoadSCGEdgeSet.find(&edge) != LoadSCGEdgeSet.end();
        else
            assert(false && "no other kind!");
        return false;
    }

    /// Get an edge via its src and dst nodes and kind
    inline SConstraintEdge* getEdge(SConstraintNode* src, SConstraintNode* dst, SConstraintEdge::SConstraintEdgeK kind)
    {
        SConstraintEdge edge(src,dst,kind);
        if(kind == SConstraintEdge::SCopy || 
            kind == SConstraintEdge::SNormalGep || kind == SConstraintEdge::SVariantGep)
        {
            auto eit = directSEdgeSet.find(&edge);
            return *eit;
        }
        else if(kind == SConstraintEdge::SAddr)
        {
            auto eit = AddrSCGEdgeSet.find(&edge);
            return *eit;
        }
        else if(kind == SConstraintEdge::SStore)
        {
            auto eit = StoreSCGEdgeSet.find(&edge);
            return *eit;
        }
        else if(kind == SConstraintEdge::SLoad)
        {
            auto eit = LoadSCGEdgeSet.find(&edge);
            return *eit;
        }
        else
        {
            assert(false && "no other kind!");
            return nullptr;
        }
    }

    ///Add a SVFIR edge into Edge map
    //@{
    /// Add Address edge
    AddrSCGEdge* addAddrSCGEdge(NodeID src, NodeID dst);
    AddrSCGEdge* removeAddrSCGEdgeByFlat(NodeID src, NodeID dst);
    AddrSCGEdge* retargetAddrSCGEdge(AddrSCGEdge* oldSEdge, NodeID src, NodeID dst);
    /// Add Copy edge
    CopySCGEdge* addCopySCGEdge(NodeID src, NodeID dst);
    unsigned removeCopySCGEdgeByFlat(NodeID src, NodeID dst);
    CopySCGEdge* retargetCopySCGEdge(CopySCGEdge* oldSEdge, NodeID src, NodeID dst);
    /// Add Gep edge
    NormalGepSCGEdge* addNormalGepSCGEdge(NodeID src, NodeID dst, const AccessPath& ap);
    NormalGepSCGEdge* removeNormalGepSCGEdgeByFlat(NodeID src, NodeID dst, const AccessPath& ap);
    NormalGepSCGEdge* retargetNormalGepSCGEdge(NormalGepSCGEdge* oldSEdge, NodeID src, NodeID dst, const AccessPath& ap);
    
    VariantGepSCGEdge* addVariantGepSCGEdge(NodeID src, NodeID dst);
    VariantGepSCGEdge* removeVariantGepSCGEdgeByFlat(NodeID src, NodeID dst);
    VariantGepSCGEdge* retargetVariantGepSCGEdge(VariantGepSCGEdge* oldSEdge, NodeID src, NodeID dst);
    /// Add Load edge
    LoadSCGEdge* addLoadSCGEdge(NodeID src, NodeID dst);
    LoadSCGEdge* removeLoadSCGEdgeByFlat(NodeID src, NodeID dst);
    LoadSCGEdge* retargetLoadSCGEdge(LoadSCGEdge* oldSEdge, NodeID src, NodeID dst);
    /// Add Store edge
    StoreSCGEdge* addStoreSCGEdge(NodeID src, NodeID dst);
    StoreSCGEdge* removeStoreSCGEdgeByFlat(NodeID src, NodeID dst);
    StoreSCGEdge* retargetStoreSCGEdge(StoreSCGEdge* oldSEdge, NodeID src, NodeID dst);
    //@}

    ///Get SVFIR edge
    //@{
    /// Get Address edges
    inline SConstraintEdge::SConstraintEdgeSetTy& getAddrSCGEdges()
    {
        return AddrSCGEdgeSet;
    }
    /// Get Copy/call/ret/gep edges
    inline SConstraintEdge::SConstraintEdgeSetTy& getDirectSCGEdges()
    {
        return directSEdgeSet;
    }
    /// Get Load edges
    inline SConstraintEdge::SConstraintEdgeSetTy& getLoadSCGEdges()
    {
        return LoadSCGEdgeSet;
    }
    /// Get Store edges
    inline SConstraintEdge::SConstraintEdgeSetTy& getStoreSCGEdges()
    {
        return StoreSCGEdgeSet;
    }
    //@}

    /// Used for cycle elimination
    //@{
    /// Remove edge from old dst target, change edge dst id and add modifed edge into new dst
    void reTargetDstOfEdge(SConstraintEdge* edge, SConstraintNode* newDstNode);
    /// Remove edge from old src target, change edge dst id and add modifed edge into new src
    void reTargetSrcOfEdge(SConstraintEdge* edge, SConstraintNode* newSrcNode);
    /// Remove addr edge from their src and dst edge sets
    void removeAddrEdge(AddrSCGEdge* edge);
    /// Remove direct edge from their src and dst edge sets
    void removeDirectEdge(SConstraintEdge* edge);
    /// Remove load edge from their src and dst edge sets
    void removeLoadEdge(LoadSCGEdge* edge);
    /// Remove store edge from their src and dst edge sets
    void removeStoreEdge(StoreSCGEdge* edge);
    /// SCC break detection
    unsigned sccBreakDetect(NodeID src, NodeID dst, FConstraintEdge::FConstraintEdgeK kind);
    ConstraintGraph* buildTempG(NodeID rep, NodeID src, NodeID dst, FConstraintEdge::FConstraintEdgeK kind);
    void sccRestore(NodeID rep);
    void restoreEdge(SConstraintNode* repNode);
    void restoreAddr(SConstraintNode* repNode);
    void restoreLoad(SConstraintNode* repNode);
    void restoreStore(SConstraintNode* repNode);
    //@}

    /// SCC rep/sub nodes methods
    //@{
    inline NodeID sccRepNode(NodeID id) const
    {
        NodeToRepMap::const_iterator it = nodeToRepMap.find(id);
        if(it==nodeToRepMap.end())
            return id;
        else
            return it->second;
    }
    inline NodeBS& sccSubNodes(NodeID id)
    {
        nodeToSubsMap[id].set(id);
        return nodeToSubsMap[id];
    }
    inline void setRep(NodeID node, NodeID rep)
    {
        nodeToRepMap[node] = rep;
    }
    inline void setSubs(NodeID node, NodeBS& subs)
    {
        nodeToSubsMap[node] |= subs;
    }
    inline void resetSubs(NodeID node)
    {
        nodeToSubsMap.erase(node);
    }
    inline NodeBS& getSubs(NodeID node)
    {
        return nodeToSubsMap[node];
    }
    inline NodeID getRep(NodeID node)
    {
        return nodeToRepMap[node];
    }
    inline void resetRep(NodeID node)
    {
        nodeToRepMap.erase(node);
    }
    //@}

    /// Move incoming direct edges of a sub node which is outside the SCC to its rep node
    /// Remove incoming direct edges of a sub node which is inside the SCC from its rep node
    /// Return TRUE if there's a gep edge inside this SCC (PWC).
    bool moveInEdgesToRepNode(SConstraintNode*node, SConstraintNode* rep );

    /// Move outgoing direct edges of a sub node which is outside the SCC to its rep node
    /// Remove outgoing direct edges of sub node which is inside the SCC from its rep node
    /// Return TRUE if there's a gep edge inside this SCC (PWC).
    bool moveOutEdgesToRepNode(SConstraintNode*node, SConstraintNode* rep );

    /// Move incoming/outgoing direct edges of a sub node to its rep node
    /// Return TRUE if there's a gep edge inside this SCC (PWC).
    inline bool moveEdgesToRepNode(SConstraintNode*node, SConstraintNode* rep )
    {
        bool gepIn = moveInEdgesToRepNode(node, rep);
        bool gepOut = moveOutEdgesToRepNode(node, rep);
        return (gepIn || gepOut);
    }

    /// Check if a given edge is a NormalGepCGEdge with 0 offset.
    inline bool isZeroOffsettedGepSCGEdge(SConstraintEdge *edge) const
    {
        if (NormalGepSCGEdge *normalGepSCGEdge = SVFUtil::dyn_cast<NormalGepSCGEdge>(edge))
            if (0 == normalGepSCGEdge->getConstantFieldIdx())
                return true;
        return false;
    }

    /// Wrappers for invoking SVFIR methods
    //@{
    inline const SVFIR::CallSiteToFunPtrMap& getIndirectCallsites() const
    {
        return pag->getIndirectCallsites();
    }
    inline NodeID getBlackHoleNode()
    {
        return pag->getBlackHoleNode();
    }
    inline bool isBlkObjOrConstantObj(NodeID id)
    {
        return pag->isBlkObjOrConstantObj(id);
    }
    inline NodeBS& getAllFieldsObjVars(NodeID id)
    {
        return pag->getAllFieldsObjVars(id);
    }
    inline NodeID getBaseObjVar(NodeID id)
    {
        return pag->getBaseObjVar(id);
    }
    inline bool isSingleFieldObj(NodeID id) const
    {
        const MemObj* mem = pag->getBaseObj(id);
        return (mem->getMaxFieldOffsetLimit() == 1);
    }
    /// Get a field of a memory object
    inline NodeID getGepObjVar(NodeID id, const APOffset& apOffset)
    { 
        /// TODO: Separate get and add
        NodeID gep =  pag->getGepObjVar(id, apOffset);
        /// Create a node when it is (1) not exist on graph and (2) not merged
        if(sccRepNode(gep)==gep && hasSConstraintNode(gep)==false)
            addSConstraintNode(new SConstraintNode(gep),gep);
        return gep;
    }
    /// Get a field-insensitive node of a memory object
    inline NodeID getFIObjVar(NodeID id)
    {
        NodeID fi = pag->getFIObjVar(id);
        /// The fi obj in PAG must be either an existing node or merged to another rep node in ConsG
        assert((hasSConstraintNode(fi) || sccRepNode(fi) != fi) && "non-existing fi obj??");
        return fi;
    }
    //@}

    /// Check/Set PWC (positive weight cycle) flag
    //@{
    inline bool isPWCNode(NodeID nodeId)
    {
        return getSConstraintNode(nodeId)->isPWCNode();
    }
    inline void setPWCNode(NodeID nodeId)
    {
        getSConstraintNode(nodeId)->setPWCNode();
    }
    //@}

    /// Add/get nodes to be collapsed
    //@{
    inline bool hasNodesToBeCollapsed() const
    {
        return (!nodesToBeCollapsed.empty());
    }
    inline void addNodeToBeCollapsed(NodeID id)
    {
        nodesToBeCollapsed.push(id);
    }
    inline NodeID getNextCollapseNode()
    {
        return nodesToBeCollapsed.pop();
    }
    //@}

    /// Dump graph into dot file
    void dump(std::string name);
    /// Print CG into terminal
    void print();

    /// View graph from the debugger.
    void view();
};

} // End namespace SVF

namespace SVF
{
/* !
 * GenericGraphTraits specializations for the generic graph algorithms.
 * Provide graph traits for traversing from a constraint node using standard graph traversals.
 */
template<> struct GenericGraphTraits<SVF::SConstraintNode*> : public GenericGraphTraits<SVF::GenericNode<SVF::SConstraintNode,SVF::SConstraintEdge>*  >
{
};

/// Inverse GenericGraphTraits specializations for Value flow node, it is used for inverse traversal.
template<>
struct GenericGraphTraits<Inverse<SVF::SConstraintNode *> > : public GenericGraphTraits<Inverse<SVF::GenericNode<SVF::SConstraintNode,SVF::SConstraintEdge>* > >
{
};

template<> struct GenericGraphTraits<SVF::SConstraintGraph*> : public GenericGraphTraits<SVF::GenericGraph<SVF::SConstraintNode,SVF::SConstraintEdge>* >
{
    typedef SVF::SConstraintNode *NodeRef;
};

} // End namespace SVF

#endif /* SUPERCONSG_H_ */