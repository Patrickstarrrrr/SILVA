#ifndef INCLUDE_WPA_ANDERSENINC_H_
#define INCLUDE_WPA_ANDERSENINC_H_

#include "WPA/Andersen.h"
#include "Graphs/SuperConsG.h"
#include "Graphs/FlatConsG.h"

namespace SVF{


// class AndersenInc : public AndersenWaveDiff
typedef WPASolver<SConstraintGraph*> WPASConstraintSolver;
class AndersenInc: public WPASConstraintSolver, public BVDataPTAImpl
{

private:
    static AndersenInc* incpta;


protected:
    /// Flat Constraint Graph
    FConstraintGraph* fCG;
    /// Super Constraint Graph
    SConstraintGraph* sCG;

public:
    
    AndersenInc(SVFIR* _pag, PTATY type = Andersen_INC, bool alias_check = true)
    // AndersenWaveDiff(_pag, type, alias_check), fCG(nullptr), sCG(nullptr)
        : BVDataPTAImpl(_pag, type, alias_check)
    {
        iterationForPrintStat = OnTheFlyIterBudgetForStat;
    }

    ~AndersenInc();

    /// Andersen analysis
    virtual void analyze() override;

    /// Initialize analysis
    virtual void initialize() override;

    /// Finalize analysis
    virtual void finalize() override;

    /// Methods for support type inquiry through isa, cast, and dyn_cast:
    //@{
    static inline bool classof(const AndersenInc *)
    {
        return true;
    }
    static inline bool classof(const PointerAnalysis *pta)
    {
        return (pta->getAnalysisTy() == Andersen_INC);
    }
    //@}

    inline FConstraintGraph* getFConstraintGraph() 
    {
        return fCG;
    }
    inline SConstraintGraph* getSConstraintGraph()
    {
        return sCG;
    }

    /// dump statistics
    inline void printStat()
    {
        PointerAnalysis::dumpStat();
    }

    virtual void normalizePointsTo() override;

    /// remove redundant gepnodes in constraint graph
    void cleanConsCG(NodeID id);

    NodeBS redundantGepNodes;

    /// Statistics
    //@{
    static u32_t numOfProcessedAddr;   /// Number of processed Addr edge
    static u32_t numOfProcessedCopy;   /// Number of processed Copy edge
    static u32_t numOfProcessedGep;    /// Number of processed Gep edge
    static u32_t numOfProcessedLoad;   /// Number of processed Load edge
    static u32_t numOfProcessedStore;  /// Number of processed Store edge
    static u32_t numOfSfrs;
    static u32_t numOfFieldExpand;

    static u32_t numOfSCCDetection;
    static double timeOfSCCDetection;
    static double timeOfSCCMerges;
    static double timeOfCollapse;
    static u32_t AveragePointsToSetSize;
    static u32_t MaxPointsToSetSize;
    static double timeOfProcessCopyGep;
    static double timeOfProcessLoadStore;
    static double timeOfUpdateCallGraph;
    //@}
    typedef SCCDetection<SConstraintGraph*> CGSCC;
    typedef OrderedMap<CallSite, NodeID> CallSite2DummyValPN;

    /// Reset data
    inline void resetData()
    {
        AveragePointsToSetSize = 0;
        MaxPointsToSetSize = 0;
        timeOfProcessCopyGep = 0;
        timeOfProcessLoadStore = 0;
    }

    /// SCC methods
    //@{
    inline NodeID sccRepNode(NodeID id) const
    {
        return sCG->sccRepNode(id);
    }
    inline NodeBS& sccSubNodes(NodeID repId)
    {
        return sCG->sccSubNodes(repId);
    }
    //@}

    /// Operation of points-to set
    virtual inline const PointsTo& getPts(NodeID id)
    {
        return getPTDataTy()->getPts(sccRepNode(id));
    }
    virtual inline bool unionPts(NodeID id, const PointsTo& target)
    {
        id = sccRepNode(id);
        return getPTDataTy()->unionPts(id, target);
    }
    virtual inline bool unionPts(NodeID id, NodeID ptd)
    {
        id = sccRepNode(id);
        ptd = sccRepNode(ptd);
        return getPTDataTy()->unionPts(id,ptd);
    }


    void dumpTopLevelPtsTo();

    inline void setDetectPWC(bool flag)
    {
        Options::DetectPWC.setValue(flag);
    }

protected:
    CallSite2DummyValPN callsite2DummyValPN;        ///< Map an instruction to a dummy obj which created at an indirect callsite, which invokes a heap allocator
    void heapAllocatorViaIndCall(CallSite cs,NodePairSet &cpySrcNodes);

    /// Handle diff points-to set.
    virtual inline void computeDiffPts(NodeID id)
    {
        if (Options::DiffPts())
        {
            NodeID rep = sccRepNode(id);
            getDiffPTDataTy()->computeDiffPts(rep, getDiffPTDataTy()->getPts(rep));
        }
    }
    virtual inline const PointsTo& getDiffPts(NodeID id)
    {
        NodeID rep = sccRepNode(id);
        if (Options::DiffPts())
            return getDiffPTDataTy()->getDiffPts(rep);
        else
            return getPTDataTy()->getPts(rep);
    }

    /// Handle propagated points-to set.
    inline void updatePropaPts(NodeID dstId, NodeID srcId)
    {
        if (!Options::DiffPts())
            return;
        NodeID srcRep = sccRepNode(srcId);
        NodeID dstRep = sccRepNode(dstId);
        getDiffPTDataTy()->updatePropaPtsMap(srcRep, dstRep);
    }
    inline void clearPropaPts(NodeID src)
    {
        if (Options::DiffPts())
        {
            NodeID rep = sccRepNode(src);
            getDiffPTDataTy()->clearPropaPts(rep);
        }
    }

    virtual void initWorklist() {}

    /// Override WPASolver function in order to use the default solver
    // virtual void processNode(NodeID nodeId);

public:
    static AndersenInc* createAndersenInc(SVFIR* _pag)
    {
        if (incpta == nullptr)
        {
            incpta = new AndersenInc(_pag, Andersen_INC, false);
            incpta->analyze();
            return incpta;
        }
        return incpta;
    }
    static void releaseAndersenInc()
    {
        if (incpta)
            delete incpta;
        incpta = nullptr;
    }

    
    /// handling various constraints
    //@{
    virtual void processAllAddr();

    virtual bool processLoad(NodeID, const SConstraintEdge* load);
    virtual bool processStore(NodeID, const SConstraintEdge* store);
    virtual bool processCopy(NodeID, const SConstraintEdge* edge);
    virtual bool processGep(NodeID, const GepSCGEdge* edge);
    virtual void handleCopyGep(SConstraintNode* node);
    virtual void handleLoadStore(SConstraintNode* node);
    virtual void processAddr(const AddrSCGEdge* addr);    
    virtual bool processGepPts(const PointsTo& pts, const GepSCGEdge* edge);
    //@}

    /// Add copy edge on constraint graph
    virtual inline bool addCopyEdge(NodeID src, NodeID dst)
    {
        fCG->addCopyFCGEdge(src, dst);
        if (sCG->addCopySCGEdge(src, dst))
        {
            updatePropaPts(src, dst);
            return true;
        }
        return false;
    }

    /// Update call graph for the input indirect callsites
    virtual bool updateCallGraph(const CallSiteToFunPtrMap& callsites);

    /// Connect formal and actual parameters for indirect callsites
    void connectCaller2CalleeParams(CallSite cs, const SVFFunction* F, NodePairSet& cpySrcNodes);


    /// Merge sub node to its rep
    virtual void mergeNodeToRep(NodeID nodeId, NodeID newRepId);
    virtual bool mergeSrcToTgt(NodeID srcId, NodeID tgtId);
    /// Merge sub node in a SCC cycle to their rep node
    //@{
    virtual void mergeSccNodes(NodeID repNodeId, const NodeBS& subNodes);
    virtual void mergeSccCycle();
    //@}
    /// Collapse a field object into its base for field insensitive anlaysis
    //@{
    virtual void collapsePWCNode(NodeID nodeId);
    virtual void collapseFields();
    virtual bool collapseNodePts(NodeID nodeId);
    virtual bool collapseField(NodeID nodeId);
    //@}

    /// Updates subnodes of its rep, and rep node of its subs
    void updateNodeRepAndSubs(NodeID nodeId,NodeID newRepId);
    
    /// SCC detection
    virtual NodeStack& SCCDetect();

    
    /// Get PTA name
    virtual const std::string PTAName() const
    {
        return "AndersenInc";
    }
    

   

    virtual void solveWorklist();
    virtual void processNode(NodeID nodeId);
    virtual void postProcessNode(NodeID nodeId);
    virtual bool handleLoad(NodeID id, const SConstraintEdge* load); /// TODO: --wjy
    virtual bool handleStore(NodeID id, const SConstraintEdge* store);/// TODO: --wjy
    virtual bool addCopyEdgeByComplexEdge(NodeID fsrc, NodeID fdst, FConstraintEdge* complexEdge);

}; // End class AndersenInc

} // End namespace SVF

#endif /*INCLUDE_WPA_ANDERSENINC_H_*/