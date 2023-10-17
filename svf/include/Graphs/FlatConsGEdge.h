
#ifndef FLATCONSGEDGE_H_
#define FLATCONSGEDGE_H_

#include "SVFIR/SVFIR.h"
#include "Util/WorkList.h"

#include <map>
#include <set>

namespace SVF
{

class FConstraintNode;

typedef GenericEdge<FConstraintNode> GenericFConsEdgeTy;
class FConstraintEdge : public GenericFConsEdgeTy
{

public:

    enum FConstraintEdgeK
    {
        FAddr, FCopy, FStore, FLoad, FNormalGep, FVariantGep
    };

private:
    EdgeID edgeId;
public:
    FConstraintEdge(FConstraintNode* s, FConstraintNode* d, FConstraintEdgeK k, EdgeID id = 0) : GenericFConsEdgeTy(s,d,k),edgeId(id)
    {
    }
    ~FConstraintEdge()
    {
    }

    inline EdgeID getEdgeID() const
    {
        return edgeId;
    }

    /// ClassOf
    static inline bool classof(const GenericFConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == FAddr ||
               edge->getEdgeKind() == FCopy ||
               edge->getEdgeKind() == FStore ||
               edge->getEdgeKind() == FLoad ||
               edge->getEdgeKind() == FNormalGep ||
               edge->getEdgeKind() == FVariantGep;
    }

    typedef GenericNode<FConstraintNode,FConstraintEdge>::GEdgeSetTy FConstraintEdgeSetTy;
    typedef GenericNode<FConstraintNode,FConstraintEdge>::GEdgeUOSetTy FConstraintEdgeUOSetTy;
};

/*!
 * Addr edge
 */
class AddrFCGEdge: public FConstraintEdge
{
private:
    AddrFCGEdge();
    AddrFCGEdge(const AddrFCGEdge &);
    void operator=(const AddrFCGEdge &);
public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const AddrFCGEdge *)
    {
        return true;
    }
    static inline bool classof(const FConstraintEdge *edge)
    {
        return edge->getEdgeKind() == FAddr;
    }
    static inline bool classof(const GenericFConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == FAddr;
    }
    //@}

    /// constructor
    AddrFCGEdge(FConstraintNode* s, FConstraintNode* d, EdgeID id);
};

/*!
 * Copy edge
 */
class CopyFCGEdge: public FConstraintEdge
{
private:
    CopyFCGEdge();                      ///< place holder
    CopyFCGEdge(const CopyFCGEdge &);  ///< place holder
    void operator=(const CopyFCGEdge &); ///< place holder
    FConstraintEdgeUOSetTy complexEdgeSet;
public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const CopyFCGEdge *)
    {
        return true;
    }
    static inline bool classof(const FConstraintEdge *edge)
    {
        return edge->getEdgeKind() == FCopy;
    }
    static inline bool classof(const GenericFConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == FCopy;
    }
    //@}

    /// constructor
    CopyFCGEdge(FConstraintNode* s, FConstraintNode* d, EdgeID id) : FConstraintEdge(s,d,FCopy,id)
    {
    }
    inline FConstraintEdge::FConstraintEdgeUOSetTy& getComplexEdgeSet()
    {
        return complexEdgeSet;
    }
    inline bool addComplexEdge(FConstraintEdge* ce)
    {
        return complexEdgeSet.insert(ce).second;
    }
    inline void removeComplexEdge(FConstraintEdge* ce)
    {
        complexEdgeSet.erase(ce);
    }
};

/*!
 * Store edge
 */
class StoreFCGEdge: public FConstraintEdge
{
private:
    StoreFCGEdge();                      ///< place holder
    StoreFCGEdge(const StoreFCGEdge &);  ///< place holder
    void operator=(const StoreFCGEdge &); ///< place holder

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const StoreFCGEdge *)
    {
        return true;
    }
    static inline bool classof(const FConstraintEdge *edge)
    {
        return edge->getEdgeKind() == FStore;
    }
    static inline bool classof(const GenericFConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == FStore;
    }
    //@}

    /// constructor
    StoreFCGEdge(FConstraintNode* s, FConstraintNode* d, EdgeID id) : FConstraintEdge(s,d,FStore,id)
    {
    }
};

/*!
 * Load edge
 */
class LoadFCGEdge: public FConstraintEdge
{
private:
    LoadFCGEdge();                      ///< place holder
    LoadFCGEdge(const LoadFCGEdge &);  ///< place holder
    void operator=(const LoadFCGEdge &); ///< place holder

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const LoadFCGEdge *)
    {
        return true;
    }
    static inline bool classof(const FConstraintEdge *edge)
    {
        return edge->getEdgeKind() == FLoad;
    }
    static inline bool classof(const GenericFConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == FLoad;
    }
    //@}

    /// Constructor
    LoadFCGEdge(FConstraintNode* s, FConstraintNode* d, EdgeID id) : FConstraintEdge(s,d,FLoad,id)
    {
    }
};

/*!
 * Gep edge
 */
class GepFCGEdge: public FConstraintEdge
{
private:
    GepFCGEdge();                      ///< place holder
    GepFCGEdge(const GepFCGEdge &);  ///< place holder
    void operator=(const GepFCGEdge &); ///< place holder

protected:

    /// Constructor
    GepFCGEdge(FConstraintNode* s, FConstraintNode* d, FConstraintEdgeK k, EdgeID id)
        : FConstraintEdge(s,d,k,id)
    {

    }

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const GepFCGEdge *)
    {
        return true;
    }
    static inline bool classof(const FConstraintEdge *edge)
    {
        return edge->getEdgeKind() == FNormalGep ||
               edge->getEdgeKind() == FVariantGep;
    }
    static inline bool classof(const GenericFConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == FNormalGep ||
               edge->getEdgeKind() == FVariantGep;
    }
    //@}

};

/*!
 * NormalGep edge
 */
class NormalGepFCGEdge : public GepFCGEdge
{
private:
    NormalGepFCGEdge();                      ///< place holder
    NormalGepFCGEdge(const NormalGepFCGEdge &);  ///< place holder
    void operator=(const NormalGepFCGEdge &); ///< place holder

    AccessPath ap;	///< Access path of the gep edge

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const NormalGepFCGEdge *)
    {
        return true;
    }
    static inline bool classof(const GepFCGEdge *edge)
    {
        return edge->getEdgeKind() == FNormalGep;
    }
    static inline bool classof(const FConstraintEdge *edge)
    {
        return edge->getEdgeKind() == FNormalGep;
    }
    static inline bool classof(const GenericFConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == FNormalGep;
    }
    //@}

    /// Constructor
    NormalGepFCGEdge(FConstraintNode* s, FConstraintNode* d, const AccessPath& ap,
                    EdgeID id)
        : GepFCGEdge(s, d, FNormalGep, id), ap(ap)
    {
    }

    /// Get location set of the gep edge
    inline const AccessPath& getAccessPath() const
    {
        return ap;
    }

    /// Get location set of the gep edge
    inline APOffset getConstantFieldIdx() const
    {
        return ap.getConstantFieldIdx();
    }

};

/*!
 * VariantGep edge
 */
class VariantGepFCGEdge : public GepFCGEdge
{
private:
    VariantGepFCGEdge();                      ///< place holder
    VariantGepFCGEdge(const VariantGepFCGEdge &);  ///< place holder
    void operator=(const VariantGepFCGEdge &); ///< place holder

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const VariantGepFCGEdge *)
    {
        return true;
    }
    static inline bool classof(const GepFCGEdge *edge)
    {
        return edge->getEdgeKind() == FVariantGep;
    }
    static inline bool classof(const FConstraintEdge *edge)
    {
        return edge->getEdgeKind() == FVariantGep;
    }
    static inline bool classof(const GenericFConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == FVariantGep;
    }
    //@}

    /// Constructor
    VariantGepFCGEdge(FConstraintNode* s, FConstraintNode* d, EdgeID id)
        : GepFCGEdge(s,d,FVariantGep,id)
    {}
};

} // End namespace SVF

#endif /* FLATCONSGEDGE_H_ */
 