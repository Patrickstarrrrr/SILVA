
#ifndef FLATCONSG_H_
#define FLATCONSG_H_

#include "Graphs/FlatConsGEdge.h"
#include "Graphs/FlatConsGNode.h"


namespace SVF
{

class FConstraintGraph : public GenericGraph<FConstraintNode, FConstraintEdge>
{

public:
    typedef OrderedMap<NodeID, FConstraintNode *> FConstraintNodeIDToNodeMapTy;
    typedef FConstraintEdge::FConstraintEdgeSetTy::iterator FConstraintNodeIter;
    typedef Map<NodeID, NodeID> NodeToRepMap;
    typedef Map<NodeID, NodeBS> NodeToSubsMap;
    typedef FIFOWorkList<NodeID> WorkList;

protected:
    SVFIR* pag;
    NodeToRepMap nodeToRepMap;
    NodeToSubsMap nodeToSubsMap;
    WorkList nodesToBeCollapsed;
    EdgeID edgeIndex;

    FConstraintEdge::FConstraintEdgeSetTy AddrFCGEdgeSet;
    FConstraintEdge::FConstraintEdgeSetTy directFEdgeSet;
    FConstraintEdge::FConstraintEdgeSetTy LoadFCGEdgeSet;
    FConstraintEdge::FConstraintEdgeSetTy StoreFCGEdgeSet;

    void buildFCG();

    void destroy();

    inline SVFStmt::SVFStmtSetTy& getPAGEdgeSet(SVFStmt::PEDGEK kind)
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
    FConstraintGraph(SVFIR* p): pag(p), edgeIndex(0)
    {
        buildFCG();
    }
    /// Destructor
    virtual ~FConstraintGraph()
    {
        destroy();
    }

    /// Get/add/remove constraint node
    //@{
    inline FConstraintNode* getFConstraintNode(NodeID id) const
    {
        // id = sccRepNode(id);
        return getGNode(id);
    }
    inline void addFConstraintNode(FConstraintNode* node, NodeID id)
    {
        addGNode(id,node);
    }
    inline bool hasFConstraintNode(NodeID id) const
    {
        // id = sccRepNode(id);
        return hasGNode(id);
    }
    inline void removeFConstraintNode(FConstraintNode* node)
    {
        removeGNode(node);
    }
    //@}

    //// Return true if this edge exits
    inline bool hasEdge(FConstraintNode* src, FConstraintNode* dst, FConstraintEdge::FConstraintEdgeK kind)
    {
        FConstraintEdge edge(src,dst,kind);
        if(kind == FConstraintEdge::FCopy ||
                kind == FConstraintEdge::FNormalGep || kind == FConstraintEdge::FVariantGep)
            return directFEdgeSet.find(&edge) != directFEdgeSet.end();
        else if(kind == FConstraintEdge::FAddr)
            return AddrFCGEdgeSet.find(&edge) != AddrFCGEdgeSet.end();
        else if(kind == FConstraintEdge::FStore)
            return StoreFCGEdgeSet.find(&edge) != StoreFCGEdgeSet.end();
        else if(kind == FConstraintEdge::FLoad)
            return LoadFCGEdgeSet.find(&edge) != LoadFCGEdgeSet.end();
        else
            assert(false && "no other kind!");
        return false;
    }

    /// Get an edge via its src and dst nodes and kind
    inline FConstraintEdge* getFEdgeOrNullptr(FConstraintNode* src, FConstraintNode* dst, FConstraintEdge::FConstraintEdgeK kind)
    {
        FConstraintEdge edge(src,dst,kind);
        if(kind == FConstraintEdge::FCopy || kind == FConstraintEdge::FNormalGep || kind == FConstraintEdge::FVariantGep)
        {
            auto eit = directFEdgeSet.find(&edge);
            if (eit == directFEdgeSet.end())
                return nullptr;
            return *eit;
        }
        else if(kind == FConstraintEdge::FAddr)
        {
            auto eit = AddrFCGEdgeSet.find(&edge);
            if (eit == AddrFCGEdgeSet.end())
                return nullptr;
            return *eit;
        }
        else if(kind == FConstraintEdge::FStore)
        {
            auto eit = StoreFCGEdgeSet.find(&edge);
            if (eit == StoreFCGEdgeSet.end())
                return nullptr;
            return *eit;
        }
        else if(kind == FConstraintEdge::FLoad)
        {
            auto eit = LoadFCGEdgeSet.find(&edge);
            if (eit == LoadFCGEdgeSet.end())
                return nullptr;
            return *eit;
        }
        else
        {
            assert(false && "no other kind!");
            return nullptr;
        }
        // FConstraintEdge edge(src,dst,kind);
        // auto eit = directFEdgeSet.find(&edge);
        // if (eit == directFEdgeSet.end())
        //     return nullptr;
        // return *eit
    }
    
    inline FConstraintEdge* getEdge(FConstraintNode* src, FConstraintNode* dst, FConstraintEdge::FConstraintEdgeK kind)
    {
        FConstraintEdge edge(src,dst,kind);
        if(kind == FConstraintEdge::FCopy || kind == FConstraintEdge::FNormalGep || kind == FConstraintEdge::FVariantGep)
        {
            auto eit = directFEdgeSet.find(&edge);
            return *eit;
        }
        else if(kind == FConstraintEdge::FAddr)
        {
            auto eit = AddrFCGEdgeSet.find(&edge);
            return *eit;
        }
        else if(kind == FConstraintEdge::FStore)
        {
            auto eit = StoreFCGEdgeSet.find(&edge);
            return *eit;
        }
        else if(kind == FConstraintEdge::FLoad)
        {
            auto eit = LoadFCGEdgeSet.find(&edge);
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
    AddrFCGEdge* addAddrFCGEdge(NodeID src, NodeID dst);
    /// Add Copy edge
    CopyFCGEdge* addCopyFCGEdge(NodeID src, NodeID dst, FConstraintEdge* complexEdge = nullptr);
    /// Add Gep edge
    NormalGepFCGEdge* addNormalGepFCGEdge(NodeID src, NodeID dst, const AccessPath& ap);
    VariantGepFCGEdge* addVariantGepFCGEdge(NodeID src, NodeID dst);
    /// Add Load edge
    LoadFCGEdge* addLoadFCGEdge(NodeID src, NodeID dst);
    /// Add Store edge
    StoreFCGEdge* addStoreFCGEdge(NodeID src, NodeID dst);
    //@}

    ///Try to remove a SVFIR edge from Edge map
    //@{
    CopyFCGEdge* removeCopyFCGEdgeByComplex(NodeID src, NodeID dst, FConstraintEdge* complexEdge = nullptr);
    //@}

    ///Get SVFIR edge
    //@{
    /// Get Address edges
    inline FConstraintEdge::FConstraintEdgeSetTy& getAddrFCGEdges()
    {
        return AddrFCGEdgeSet;
    }
    /// Get Copy/call/ret/gep edges
    inline FConstraintEdge::FConstraintEdgeSetTy& getDirectFCGEdges()
    {
        return directFEdgeSet;
    }
    /// Get Load edges
    inline FConstraintEdge::FConstraintEdgeSetTy& getLoadFCGEdges()
    {
        return LoadFCGEdgeSet;
    }
    /// Get Store edges
    inline FConstraintEdge::FConstraintEdgeSetTy& getStoreFCGEdges()
    {
        return StoreFCGEdgeSet;
    }
    //@}

    /// Used for cycle elimination
    //@{
    // /// Remove edge from old dst target, change edge dst id and add modifed edge into new dst
    // void reTargetDstOfEdge(FConstraintEdge* edge, FConstraintNode* newDstNode);
    // /// Remove edge from old src target, change edge dst id and add modifed edge into new src
    // void reTargetSrcOfEdge(FConstraintEdge* edge, FConstraintNode* newSrcNode);
    /// Remove addr edge from their src and dst edge sets
    void removeAddrEdge(AddrFCGEdge* edge);
    /// Remove direct edge from their src and dst edge sets
    void removeDirectEdge(FConstraintEdge* edge);
    /// Remove load edge from their src and dst edge sets
    void removeLoadEdge(LoadFCGEdge* edge);
    /// Remove store edge from their src and dst edge sets
    void removeStoreEdge(StoreFCGEdge* edge);
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
    bool moveInEdgesToRepNode(FConstraintNode*node, FConstraintNode* rep );

    /// Move outgoing direct edges of a sub node which is outside the SCC to its rep node
    /// Remove outgoing direct edges of sub node which is inside the SCC from its rep node
    /// Return TRUE if there's a gep edge inside this SCC (PWC).
    bool moveOutEdgesToRepNode(FConstraintNode*node, FConstraintNode* rep );

    /// Move incoming/outgoing direct edges of a sub node to its rep node
    /// Return TRUE if there's a gep edge inside this SCC (PWC).
    inline bool moveEdgesToRepNode(FConstraintNode*node, FConstraintNode* rep )
    {
        bool gepIn = moveInEdgesToRepNode(node, rep);
        bool gepOut = moveOutEdgesToRepNode(node, rep);
        return (gepIn || gepOut);
    }

    /// Check if a given edge is a NormalGepCGEdge with 0 offset.
    inline bool isZeroOffsettedGepFCGEdge(FConstraintEdge *edge) const
    {
        if (NormalGepFCGEdge *normalGepFCGEdge = SVFUtil::dyn_cast<NormalGepFCGEdge>(edge))
            if (0 == normalGepFCGEdge->getConstantFieldIdx())
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
        // if(sccRepNode(gep)==gep && hasFConstraintNode(gep)==false) /// TODO: sccRep 
        if(hasFConstraintNode(gep)==false) /// TODO: sccRep 
            addFConstraintNode(new FConstraintNode(gep),gep);
        return gep;
    }
    /// Get a field-insensitive node of a memory object
    inline NodeID getFIObjVar(NodeID id)
    {
        NodeID fi = pag->getFIObjVar(id);
        /// The fi obj in PAG must be either an existing node or merged to another rep node in ConsG
        assert((hasFConstraintNode(fi) || sccRepNode(fi) != fi) && "non-existing fi obj??"); /// TODO: sccRep 
        return fi;
    }
    //@}

    /// Check/Set PWC (positive weight cycle) flag
    //@{
    inline bool isPWCNode(NodeID nodeId)
    {
        return getFConstraintNode(nodeId)->isPWCNode();
    }
    inline void setPWCNode(NodeID nodeId)
    {
        getFConstraintNode(nodeId)->setPWCNode();
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
template<> struct GenericGraphTraits<SVF::FConstraintNode*> : public GenericGraphTraits<SVF::GenericNode<SVF::FConstraintNode,SVF::FConstraintEdge>*  >
{
};

/// Inverse GenericGraphTraits specializations for Value flow node, it is used for inverse traversal.
template<>
struct GenericGraphTraits<Inverse<SVF::FConstraintNode *> > : public GenericGraphTraits<Inverse<SVF::GenericNode<SVF::FConstraintNode,SVF::FConstraintEdge>* > >
{
};

template<> struct GenericGraphTraits<SVF::FConstraintGraph*> : public GenericGraphTraits<SVF::GenericGraph<SVF::FConstraintNode,SVF::FConstraintEdge>* >
{
    typedef SVF::FConstraintNode *NodeRef;
};

} // End namespace SVF

#endif /* FLATCONSG_H_ */