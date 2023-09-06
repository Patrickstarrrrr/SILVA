
#ifndef FLATCONSGNODE_H_
#define FLATCONSGNODE_H_

namespace SVF
{

typedef GenericNode<FConstraintNode,FConstraintEdge> GenericFConsNodeTy;
class FConstraintNode : public GenericFConsNodeTy
{
public:
    typedef FConstraintEdge::FConstraintEdgeSetTy::iterator iterator;
    typedef FConstraintEdge::FConstraintEdgeSetTy::const_iterator const_iterator;
    bool _isPWCNode;

private:
    FConstraintEdge::FConstraintEdgeSetTy loadInEdges; ///< all incoming load edge of this node
    FConstraintEdge::FConstraintEdgeSetTy loadOutEdges; ///< all outgoing load edge of this node

    FConstraintEdge::FConstraintEdgeSetTy storeInEdges; ///< all incoming store edge of this node
    FConstraintEdge::FConstraintEdgeSetTy storeOutEdges; ///< all outgoing store edge of this node

    /// Copy/call/ret/gep incoming edge of this node,
    /// To be noted: this set is only used when SCC detection, and node merges
    FConstraintEdge::FConstraintEdgeSetTy directInEdges;
    FConstraintEdge::FConstraintEdgeSetTy directOutEdges;

    FConstraintEdge::FConstraintEdgeSetTy copyInEdges;
    FConstraintEdge::FConstraintEdgeSetTy copyOutEdges;

    FConstraintEdge::FConstraintEdgeSetTy gepInEdges;
    FConstraintEdge::FConstraintEdgeSetTy gepOutEdges;

    FConstraintEdge::FConstraintEdgeSetTy addressInEdges; ///< all incoming address edge of this node
    FConstraintEdge::FConstraintEdgeSetTy addressOutEdges; ///< all outgoing address edge of this node

public:
    NodeBS strides;
    NodeBS baseIds;

    FConstraintNode(NodeID i) : GenericFConsNodeTy(i, 0), _isPWCNode(false)
    {

    }

    /// Whether a node involves in PWC, if so, all its points-to elements should become field-insensitive.
    //@{
    inline bool isPWCNode() const
    {
        return _isPWCNode;
    }
    inline void setPWCNode()
    {
        _isPWCNode = true;
    }
    //@}

    /// Direct and Indirect SVFIR edges
    inline bool isdirectEdge(FConstraintEdge::FConstraintEdgeK kind)
    {
        return (kind == FConstraintEdge::FCopy || kind == FConstraintEdge::FNormalGep || kind == FConstraintEdge::FVariantGep );
    }
    inline bool isIndirectEdge(FConstraintEdge::FConstraintEdgeK kind)
    {
        return (kind == FConstraintEdge::FLoad || kind == FConstraintEdge::FStore);
    }

    /// Return constraint edges
    //@{
    inline const FConstraintEdge::FConstraintEdgeSetTy& getDirectInEdges() const
    {
        return directInEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getDirectOutEdges() const
    {
        return directOutEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getCopyInEdges() const
    {
        return copyInEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getCopyOutEdges() const
    {
        return copyOutEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getGepInEdges() const
    {
        return gepInEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getGepOutEdges() const
    {
        return gepOutEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getLoadInEdges() const
    {
        return loadInEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getLoadOutEdges() const
    {
        return loadOutEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getStoreInEdges() const
    {
        return storeInEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getStoreOutEdges() const
    {
        return storeOutEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getAddrInEdges() const
    {
        return addressInEdges;
    }
    inline const FConstraintEdge::FConstraintEdgeSetTy& getAddrOutEdges() const
    {
        return addressOutEdges;
    }
    //@}

    ///  Iterators
    //@{
    iterator directOutEdgeBegin();
    iterator directOutEdgeEnd();
    iterator directInEdgeBegin();
    iterator directInEdgeEnd();
    const_iterator directOutEdgeBegin() const;
    const_iterator directOutEdgeEnd() const;
    const_iterator directInEdgeBegin() const;
    const_iterator directInEdgeEnd() const;

    FConstraintEdge::FConstraintEdgeSetTy& incomingAddrEdges()
    {
        return addressInEdges;
    }
    FConstraintEdge::FConstraintEdgeSetTy& outgoingAddrEdges()
    {
        return addressOutEdges;
    }

    inline const_iterator outgoingAddrsBegin() const
    {
        return addressOutEdges.begin();
    }
    inline const_iterator outgoingAddrsEnd() const
    {
        return addressOutEdges.end();
    }
    inline const_iterator incomingAddrsBegin() const
    {
        return addressInEdges.begin();
    }
    inline const_iterator incomingAddrsEnd() const
    {
        return addressInEdges.end();
    }

    inline const_iterator outgoingLoadsBegin() const
    {
        return loadOutEdges.begin();
    }
    inline const_iterator outgoingLoadsEnd() const
    {
        return loadOutEdges.end();
    }
    inline const_iterator incomingLoadsBegin() const
    {
        return loadInEdges.begin();
    }
    inline const_iterator incomingLoadsEnd() const
    {
        return loadInEdges.end();
    }

    inline const_iterator outgoingStoresBegin() const
    {
        return storeOutEdges.begin();
    }
    inline const_iterator outgoingStoresEnd() const
    {
        return storeOutEdges.end();
    }
    inline const_iterator incomingStoresBegin() const
    {
        return storeInEdges.begin();
    }
    inline const_iterator incomingStoresEnd() const
    {
        return storeInEdges.end();
    }
    //@}

    ///  Add constraint graph edges
    //@{
    inline void addIncomingCopyEdge(CopyFCGEdge *inEdge)
    {
        addIncomingDirectEdge(inEdge);
        copyInEdges.insert(inEdge);
    }
    inline void addIncomingGepEdge(GepFCGEdge* inEdge)
    {
        addIncomingDirectEdge(inEdge);
        gepInEdges.insert(inEdge);
    }
    inline void addOutgoingCopyEdge(CopyFCGEdge *outEdge)
    {
        addOutgoingDirectEdge(outEdge);
        copyOutEdges.insert(outEdge);
    }
    inline void addOutgoingGepEdge(GepFCGEdge* outEdge)
    {
        addOutgoingDirectEdge(outEdge);
        gepOutEdges.insert(outEdge);
    }
    inline void addIncomingAddrEdge(AddrFCGEdge* inEdge)
    {
        addressInEdges.insert(inEdge);
        addIncomingEdge(inEdge);
    }
    inline void addIncomingLoadEdge(LoadFCGEdge* inEdge)
    {
        loadInEdges.insert(inEdge);
        addIncomingEdge(inEdge);
    }
    inline void addIncomingStoreEdge(StoreFCGEdge* inEdge)
    {
        storeInEdges.insert(inEdge);
        addIncomingEdge(inEdge);
    }
    inline bool addIncomingDirectEdge(FConstraintEdge* inEdge)
    {
        assert(inEdge->getDstID() == this->getId());
        bool added1 = directInEdges.insert(inEdge).second;
        bool added2 = addIncomingEdge(inEdge);
        bool both_added = added1 & added2;
        assert(both_added && "edge not added, duplicated adding!!");
        return both_added;
    }
    inline void addOutgoingAddrEdge(AddrFCGEdge* outEdge)
    {
        addressOutEdges.insert(outEdge);
        addOutgoingEdge(outEdge);
    }
    inline bool addOutgoingLoadEdge(LoadFCGEdge* outEdge)
    {
        bool added1 = loadOutEdges.insert(outEdge).second;
        bool added2 = addOutgoingEdge(outEdge);
        bool both_added = added1 & added2;
        assert(both_added && "edge not added, duplicated adding!!");
        return both_added;
    }
    inline bool addOutgoingStoreEdge(StoreFCGEdge* outEdge)
    {
        bool added1 = storeOutEdges.insert(outEdge).second;
        bool added2 = addOutgoingEdge(outEdge);
        bool both_added = added1 & added2;
        assert(both_added && "edge not added, duplicated adding!!");
        return both_added;
    }
    inline bool addOutgoingDirectEdge(FConstraintEdge* outEdge)
    {
        assert(outEdge->getSrcID() == this->getId());
        bool added1 = directOutEdges.insert(outEdge).second;
        bool added2 = addOutgoingEdge(outEdge);
        bool both_added = added1 & added2;
        assert(both_added && "edge not added, duplicated adding!!");
        return both_added;
    }
    //@}

    /// Remove constraint graph edges
    //{@
    inline bool removeOutgoingAddrEdge(AddrFCGEdge* outEdge)
    {
        u32_t num1 = addressOutEdges.erase(outEdge);
        u32_t num2 = removeOutgoingEdge(outEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeIncomingAddrEdge(AddrFCGEdge* inEdge)
    {
        u32_t num1 = addressInEdges.erase(inEdge);
        u32_t num2 = removeIncomingEdge(inEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeOutgoingDirectEdge(FConstraintEdge* outEdge)
    {
        if (SVFUtil::isa<GepFCGEdge>(outEdge))
            gepOutEdges.erase(outEdge);
        else
            copyOutEdges.erase(outEdge);
        u32_t num1 = directOutEdges.erase(outEdge);
        u32_t num2 = removeOutgoingEdge(outEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeIncomingDirectEdge(FConstraintEdge* inEdge)
    {
        if (SVFUtil::isa<GepFCGEdge>(inEdge))
            gepInEdges.erase(inEdge);
        else
            copyInEdges.erase(inEdge);
        u32_t num1 = directInEdges.erase(inEdge);
        u32_t num2 = removeIncomingEdge(inEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeOutgoingLoadEdge(LoadFCGEdge* outEdge)
    {
        u32_t num1 = loadOutEdges.erase(outEdge);
        u32_t num2 = removeOutgoingEdge(outEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeIncomingLoadEdge(LoadFCGEdge* inEdge)
    {
        u32_t num1 = loadInEdges.erase(inEdge);
        u32_t num2 = removeIncomingEdge(inEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeOutgoingStoreEdge(StoreFCGEdge* outEdge)
    {
        u32_t num1 = storeOutEdges.erase(outEdge);
        u32_t num2 = removeOutgoingEdge(outEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeIncomingStoreEdge(StoreFCGEdge* inEdge)
    {
        u32_t num1 = storeInEdges.erase(inEdge);
        u32_t num2 = removeIncomingEdge(inEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }
    //@}
};

}

#endif /* FLATCONSGNODE_H_ */