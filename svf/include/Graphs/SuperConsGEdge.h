
#ifndef SUPERCONSGEDGE_H_
#define SUPERCONSGEDGE_H_

#include "SVFIR/SVFIR.h"
#include "Util/WorkList.h"
#include "Graphs/FlatConsGEdge.h"
#include <map>
#include <set>

namespace SVF
{

class SConstraintNode;

typedef GenericEdge<SConstraintNode> GenericSConsEdgeTy;
class SConstraintEdge : public GenericSConsEdgeTy
{

public:

    enum SConstraintEdgeK
    {
        SAddr, SCopy, SStore, SLoad, SNormalGep, SVariantGep
    };

private:
    EdgeID edgeId;
    FConstraintEdge::FConstraintEdgeUOSetTy fEdgeSet;
    // bool _isRetarget;
public:
    /// Constructor
    SConstraintEdge(SConstraintNode* s, SConstraintNode* d, SConstraintEdgeK k, 
    EdgeID id = 0, FConstraintEdge* fe = nullptr, bool ir = false) : 
    GenericSConsEdgeTy(s,d,k),edgeId(id)
    {
    }
    /// Destructor
    ~SConstraintEdge()
    {
    }
    /// Return edge ID
    inline EdgeID getEdgeID() const
    {
        return edgeId;
    }
    // inline bool isRetarget() const
    // {
    //     return _isRetarget;
    // }
    // inline void setRetarget(bool ir)
    // {
    //     _isRetarget = ir;
    // }
    /// ClassOf
    static inline bool classof(const GenericSConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == SAddr ||
               edge->getEdgeKind() == SCopy ||
               edge->getEdgeKind() == SStore ||
               edge->getEdgeKind() == SLoad ||
               edge->getEdgeKind() == SNormalGep ||
               edge->getEdgeKind() == SVariantGep;
    }
    /// Constraint edge type
    typedef GenericNode<SConstraintNode,SConstraintEdge>::GEdgeSetTy SConstraintEdgeSetTy;
    typedef GenericNode<SConstraintNode,SConstraintEdge>::GEdgeUOSetTy SConstraintEdgeUOSetTy;

    /// flat Edge Set
    //@{
    inline const FConstraintEdge::FConstraintEdgeUOSetTy& getFEdgeSet() const 
    {
        return fEdgeSet;
    }
    inline bool addFEdge(FConstraintEdge* fe)
    {
        return fEdgeSet.insert(fe).second;
    }
    inline void removeFEdge(FConstraintEdge* fe)
    {
        fEdgeSet.erase(fe);
    }
    //@}

};


/*!
 * Addr edge
 */
class AddrSCGEdge: public SConstraintEdge
{
private:
    AddrSCGEdge();                      ///< place holder
    AddrSCGEdge(const AddrSCGEdge &);  ///< place holder
    void operator=(const AddrSCGEdge &); ///< place holder
public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const AddrSCGEdge *)
    {
        return true;
    }
    static inline bool classof(const SConstraintEdge *edge)
    {
        return edge->getEdgeKind() == SAddr;
    }
    static inline bool classof(const GenericSConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == SAddr;
    }
    //@}

    /// constructor
    AddrSCGEdge(SConstraintNode* s, SConstraintNode* d, EdgeID id);
};


/*!
 * Copy edge
 */
class CopySCGEdge: public SConstraintEdge
{
private:
    CopySCGEdge();                      ///< place holder
    CopySCGEdge(const CopySCGEdge &);  ///< place holder
    void operator=(const CopySCGEdge &); ///< place holder
public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const CopySCGEdge *)
    {
        return true;
    }
    static inline bool classof(const SConstraintEdge *edge)
    {
        return edge->getEdgeKind() == SCopy;
    }
    static inline bool classof(const GenericSConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == SCopy;
    }
    //@}

    /// constructor
    CopySCGEdge(SConstraintNode* s, SConstraintNode* d, EdgeID id) : SConstraintEdge(s,d,SCopy,id)
    {
    }
};

/*!
 * Store edge
 */
class StoreSCGEdge: public SConstraintEdge
{
private:
    StoreSCGEdge();                      ///< place holder
    StoreSCGEdge(const StoreSCGEdge &);  ///< place holder
    void operator=(const StoreSCGEdge &); ///< place holder

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const StoreSCGEdge *)
    {
        return true;
    }
    static inline bool classof(const SConstraintEdge *edge)
    {
        return edge->getEdgeKind() == SStore;
    }
    static inline bool classof(const GenericSConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == SStore;
    }
    //@}

    /// constructor
    StoreSCGEdge(SConstraintNode* s, SConstraintNode* d, EdgeID id) : SConstraintEdge(s,d,SStore,id)
    {
    }
};

/*!
 * Load edge
 */
class LoadSCGEdge: public SConstraintEdge
{
private:
    LoadSCGEdge();                      ///< place holder
    LoadSCGEdge(const LoadSCGEdge &);  ///< place holder
    void operator=(const LoadSCGEdge &); ///< place holder

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const LoadSCGEdge *)
    {
        return true;
    }
    static inline bool classof(const SConstraintEdge *edge)
    {
        return edge->getEdgeKind() == SLoad;
    }
    static inline bool classof(const GenericSConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == SLoad;
    }
    //@}

    /// Constructor
    LoadSCGEdge(SConstraintNode* s, SConstraintNode* d, EdgeID id) : SConstraintEdge(s,d,SLoad,id)
    {
    }
};

/*!
 * Gep edge
 */
class GepSCGEdge: public SConstraintEdge
{
private:
    GepSCGEdge();                      ///< place holder
    GepSCGEdge(const GepSCGEdge &);  ///< place holder
    void operator=(const GepSCGEdge &); ///< place holder

protected:

    /// Constructor
    GepSCGEdge(SConstraintNode* s, SConstraintNode* d, SConstraintEdgeK k, EdgeID id)
        : SConstraintEdge(s,d,k,id)
    {

    }

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const GepSCGEdge *)
    {
        return true;
    }
    static inline bool classof(const SConstraintEdge *edge)
    {
        return edge->getEdgeKind() == SNormalGep ||
               edge->getEdgeKind() == SVariantGep;
    }
    static inline bool classof(const GenericSConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == SNormalGep ||
               edge->getEdgeKind() == SVariantGep;
    }
    //@}

};

/*!
 * NormalGep edge
 */
class NormalGepSCGEdge : public GepSCGEdge
{
private:
    NormalGepSCGEdge();                      ///< place holder
    NormalGepSCGEdge(const NormalGepSCGEdge &);  ///< place holder
    void operator=(const NormalGepSCGEdge &); ///< place holder

    AccessPath ap;	///< Access path of the gep edge

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const NormalGepSCGEdge *)
    {
        return true;
    }
    static inline bool classof(const GepSCGEdge *edge)
    {
        return edge->getEdgeKind() == SNormalGep;
    }
    static inline bool classof(const SConstraintEdge *edge)
    {
        return edge->getEdgeKind() == SNormalGep;
    }
    static inline bool classof(const GenericSConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == SNormalGep;
    }
    //@}

    /// Constructor
    NormalGepSCGEdge(SConstraintNode* s, SConstraintNode* d, const AccessPath& ap,
                    EdgeID id)
        : GepSCGEdge(s, d, SNormalGep, id), ap(ap)
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
class VariantGepSCGEdge : public GepSCGEdge
{
private:
    VariantGepSCGEdge();                      ///< place holder
    VariantGepSCGEdge(const VariantGepSCGEdge &);  ///< place holder
    void operator=(const VariantGepSCGEdge &); ///< place holder

public:
    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const VariantGepSCGEdge *)
    {
        return true;
    }
    static inline bool classof(const GepSCGEdge *edge)
    {
        return edge->getEdgeKind() == SVariantGep;
    }
    static inline bool classof(const SConstraintEdge *edge)
    {
        return edge->getEdgeKind() == SVariantGep;
    }
    static inline bool classof(const GenericSConsEdgeTy *edge)
    {
        return edge->getEdgeKind() == SVariantGep;
    }
    //@}

    /// Constructor
    VariantGepSCGEdge(SConstraintNode* s, SConstraintNode* d, EdgeID id)
        : GepSCGEdge(s,d,SVariantGep,id)
    {}
};


} // End namespace SVF

#endif /* SUPERCONSGEDGE_H_ */
 