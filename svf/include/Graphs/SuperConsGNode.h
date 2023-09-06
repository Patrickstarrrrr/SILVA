
#ifndef SUPERCONSGNODE_H_
#define SUPERCONSGNODE_H_

namespace SVF
{

typedef GenericNode<SConstraintNode, SConstraintEdge> GenericSConsNodeTy;
class SConstraintNode : public GenericSConsNodeTy
{
public:
    typedef SConstraintEdge::SConstraintEdgeSetTy::iterator iterator;
    typedef SConstraintEdge::SConstraintEdgeSetTy::const_iterator const_iterator;
    bool _isPWCNode;

private:
    SConstraintEdge::SConstraintEdgeSetTy loadInEdges; ///< all incoming load edge of this node
    SConstraintEdge::SConstraintEdgeSetTy loadOutEdges; ///< all outgoing load edge of this node

    SConstraintEdge::SConstraintEdgeSetTy storeInEdges; ///< all incoming store edge of this node
    SConstraintEdge::SConstraintEdgeSetTy storeOutEdges; ///< all outgoing store edge of this node

    /// Copy/call/ret/gep incoming edge of this node,
    /// To be noted: this set is only used when SCC detection, and node merges
    SConstraintEdge::SConstraintEdgeSetTy directInEdges;
    SConstraintEdge::SConstraintEdgeSetTy directOutEdges;

    SConstraintEdge::SConstraintEdgeSetTy copyInEdges;
    SConstraintEdge::SConstraintEdgeSetTy copyOutEdges;

    SConstraintEdge::SConstraintEdgeSetTy gepInEdges;
    SConstraintEdge::SConstraintEdgeSetTy gepOutEdges;

    SConstraintEdge::SConstraintEdgeSetTy addressInEdges; ///< all incoming address edge of this node
    SConstraintEdge::SConstraintEdgeSetTy addressOutEdges; ///< all outgoing address edge of this node

public:
    NodeBS strides;
    NodeBS baseIds;

    SConstraintNode(NodeID i) : GenericSConsNodeTy(i, 0), _isPWCNode(false)
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
    inline bool isdirectEdge(SConstraintEdge::SConstraintEdgeK kind)
    {
        return (kind == SConstraintEdge::SCopy || kind == SConstraintEdge::SNormalGep || kind == SConstraintEdge::SVariantGep );
    }
    inline bool isIndirectEdge(SConstraintEdge::SConstraintEdgeK kind)
    {
        return (kind == SConstraintEdge::SLoad || kind == SConstraintEdge::SStore);
    }

    /// Return constraint edges
    //@{
    inline const SConstraintEdge::SConstraintEdgeSetTy& getDirectInEdges() const
    {
        return directInEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getDirectOutEdges() const
    {
        return directOutEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getCopyInEdges() const
    {
        return copyInEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getCopyOutEdges() const
    {
        return copyOutEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getGepInEdges() const
    {
        return gepInEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getGepOutEdges() const
    {
        return gepOutEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getLoadInEdges() const
    {
        return loadInEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getLoadOutEdges() const
    {
        return loadOutEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getStoreInEdges() const
    {
        return storeInEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getStoreOutEdges() const
    {
        return storeOutEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getAddrInEdges() const
    {
        return addressInEdges;
    }
    inline const SConstraintEdge::SConstraintEdgeSetTy& getAddrOutEdges() const
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

    SConstraintEdge::SConstraintEdgeSetTy& incomingAddrEdges()
    {
        return addressInEdges;
    }
    SConstraintEdge::SConstraintEdgeSetTy& outgoingAddrEdges()
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
    inline void addIncomingCopyEdge(CopySCGEdge *inEdge)
    {
        addIncomingDirectEdge(inEdge);
        copyInEdges.insert(inEdge);
    }
    inline void addIncomingGepEdge(GepSCGEdge* inEdge)
    {
        addIncomingDirectEdge(inEdge);
        gepInEdges.insert(inEdge);
    }
    inline void addOutgoingCopyEdge(CopySCGEdge *outEdge)
    {
        addOutgoingDirectEdge(outEdge);
        copyOutEdges.insert(outEdge);
    }
    inline void addOutgoingGepEdge(GepSCGEdge* outEdge)
    {
        addOutgoingDirectEdge(outEdge);
        gepOutEdges.insert(outEdge);
    }
    inline void addIncomingAddrEdge(AddrSCGEdge* inEdge)
    {
        addressInEdges.insert(inEdge);
        addIncomingEdge(inEdge);
    }
    inline void addIncomingLoadEdge(LoadSCGEdge* inEdge)
    {
        loadInEdges.insert(inEdge);
        addIncomingEdge(inEdge);
    }
    inline void addIncomingStoreEdge(StoreSCGEdge* inEdge)
    {
        storeInEdges.insert(inEdge);
        addIncomingEdge(inEdge);
    }
    inline bool addIncomingDirectEdge(SConstraintEdge* inEdge)
    {
        assert(inEdge->getDstID() == this->getId());
        bool added1 = directInEdges.insert(inEdge).second;
        bool added2 = addIncomingEdge(inEdge);
        bool both_added = added1 & added2;
        assert(both_added && "edge not added, duplicated adding!!");
        return both_added;
    }
    inline void addOutgoingAddrEdge(AddrSCGEdge* outEdge)
    {
        addressOutEdges.insert(outEdge);
        addOutgoingEdge(outEdge);
    }
    inline bool addOutgoingLoadEdge(LoadSCGEdge* outEdge)
    {
        bool added1 = loadOutEdges.insert(outEdge).second;
        bool added2 = addOutgoingEdge(outEdge);
        bool both_added = added1 & added2;
        assert(both_added && "edge not added, duplicated adding!!");
        return both_added;
    }
    inline bool addOutgoingStoreEdge(StoreSCGEdge* outEdge)
    {
        bool added1 = storeOutEdges.insert(outEdge).second;
        bool added2 = addOutgoingEdge(outEdge);
        bool both_added = added1 & added2;
        assert(both_added && "edge not added, duplicated adding!!");
        return both_added;
    }
    inline bool addOutgoingDirectEdge(SConstraintEdge* outEdge)
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
    inline bool removeOutgoingAddrEdge(AddrSCGEdge* outEdge)
    {
        u32_t num1 = addressOutEdges.erase(outEdge);
        u32_t num2 = removeOutgoingEdge(outEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeIncomingAddrEdge(AddrSCGEdge* inEdge)
    {
        u32_t num1 = addressInEdges.erase(inEdge);
        u32_t num2 = removeIncomingEdge(inEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeOutgoingDirectEdge(SConstraintEdge* outEdge)
    {
        if (SVFUtil::isa<GepSCGEdge>(outEdge))
            gepOutEdges.erase(outEdge);
        else
            copyOutEdges.erase(outEdge);
        u32_t num1 = directOutEdges.erase(outEdge);
        u32_t num2 = removeOutgoingEdge(outEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeIncomingDirectEdge(SConstraintEdge* inEdge)
    {
        if (SVFUtil::isa<GepSCGEdge>(inEdge))
            gepInEdges.erase(inEdge);
        else
            copyInEdges.erase(inEdge);
        u32_t num1 = directInEdges.erase(inEdge);
        u32_t num2 = removeIncomingEdge(inEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeOutgoingLoadEdge(LoadSCGEdge* outEdge)
    {
        u32_t num1 = loadOutEdges.erase(outEdge);
        u32_t num2 = removeOutgoingEdge(outEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeIncomingLoadEdge(LoadSCGEdge* inEdge)
    {
        u32_t num1 = loadInEdges.erase(inEdge);
        u32_t num2 = removeIncomingEdge(inEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeOutgoingStoreEdge(StoreSCGEdge* outEdge)
    {
        u32_t num1 = storeOutEdges.erase(outEdge);
        u32_t num2 = removeOutgoingEdge(outEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    inline bool removeIncomingStoreEdge(StoreSCGEdge* inEdge)
    {
        u32_t num1 = storeInEdges.erase(inEdge);
        u32_t num2 = removeIncomingEdge(inEdge);
        bool removed = (num1 > 0) & (num2 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }
    //@}
};


} // end namespace SVF

#endif /* SUPERCONSGNODE_H_ */