#ifndef PAGGETTER_H_
#define PAGGETTER_H_

#include "SVFIR/SVFIR.h"
#include "SVF-LLVM/BasicTypes.h"
#include "SVF-LLVM/ICFGBuilder.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVF-LLVM/LLVMUtil.h"

namespace SVF
{

class SVFModule;

class SVFIRGetter: public llvm::InstVisitor<SVFIRGetter>
{
private:
    SVFIR* pag;
    SVFModule* svfModule;
    const SVFBasicBlock* curBB;	///< Current basic block during SVFIR construction when visiting the module
    const SVFValue* curVal;	///< Current Value during SVFIR construction when visiting the module

public:
    /// Constructor
    SVFIRGetter(SVFModule* mod): pag(SVFIR::getPAG()), svfModule(mod), curBB(nullptr),curVal(nullptr)
    {
    }
    /// Destructor
    virtual ~SVFIRGetter()
    {
    }

    /// Return SVFIR
    SVFIR* getPAG() const
    {
        return pag;
    }

    /// Get different kinds of node
    //@{
    // GetValNode - Return the value node according to a LLVM Value.
    NodeID getValueNode(const Value* V)
    {
        // first handle gep edge if val if a constant expression
        // processCE(V);

        // strip off the constant cast and return the value node
        SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(V);
        return pag->getValueNode(svfVal);
    }

    /// GetObject - Return the object node (stack/global/heap/function) according to a LLVM Value
    inline NodeID getObjectNode(const Value* V)
    {
        SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(V);
        return pag->getObjectNode(svfVal);
    }

    /// getReturnNode - Return the node representing the unique return value of a function.
    inline NodeID getReturnNode(const SVFFunction *func)
    {
        return pag->getReturnNode(func);
    }

    /// getVarargNode - Return the node representing the unique variadic argument of a function.
    inline NodeID getVarargNode(const SVFFunction *func)
    {
        return pag->getVarargNode(func);
    }
    //@}
    
    /// Our visit overrides.
    //@{
    // Instructions that cannot be folded away.
    virtual void visitAllocaInst(AllocaInst &AI);
    void visitPHINode(PHINode &I);
    void visitStoreInst(StoreInst &I);
    void visitLoadInst(LoadInst &I);
    void visitGetElementPtrInst(GetElementPtrInst &I);
    void visitCallInst(CallInst &I);
    void visitInvokeInst(InvokeInst &II);
    void visitCallBrInst(CallBrInst &I);
    void visitCallSite(CallBase* cs);
    void visitReturnInst(ReturnInst &I);
    void visitCastInst(CastInst &I);
    void visitSelectInst(SelectInst &I);
    void visitExtractValueInst(ExtractValueInst  &EVI);
    void visitBranchInst(BranchInst &I);
    void visitSwitchInst(SwitchInst &I);
    void visitInsertValueInst(InsertValueInst &I)
    {
        addBlackHoleAddrEdge(getValueNode(&I));
    }
    // TerminatorInst and UnwindInst have been removed since llvm-8.0.0
    // void visitTerminatorInst(TerminatorInst &TI) {}
    // void visitUnwindInst(UnwindInst &I) { /*returns void*/}

    void visitBinaryOperator(BinaryOperator &I);
    void visitUnaryOperator(UnaryOperator &I);
    void visitCmpInst(CmpInst &I);

    /// TODO: var arguments need to be handled.
    /// https://llvm.org/docs/LangRef.html#id1911
    void visitVAArgInst(VAArgInst&);
    void visitVACopyInst(VACopyInst&) {}
    void visitVAEndInst(VAEndInst&) {}
    void visitVAStartInst(VAStartInst&) {}

    /// <result> = freeze ty <val>
    /// If <val> is undef or poison, ‘freeze’ returns an arbitrary, but fixed value of type `ty`
    /// Otherwise, this instruction is a no-op and returns the input <val>
    void visitFreezeInst(FreezeInst& I);

    void visitExtractElementInst(ExtractElementInst &I);

    void visitInsertElementInst(InsertElementInst &I)
    {
        addBlackHoleAddrEdge(getValueNode(&I));
    }
    void visitShuffleVectorInst(ShuffleVectorInst &I)
    {
        addBlackHoleAddrEdge(getValueNode(&I));
    }
    void visitLandingPadInst(LandingPadInst &I)
    {
        addBlackHoleAddrEdge(getValueNode(&I));
    }

    /// Instruction not that often
    void visitResumeInst(ResumeInst&)   /*returns void*/
    {
    }
    void visitUnreachableInst(UnreachableInst&)   /*returns void*/
    {
    }
    void visitFenceInst(FenceInst &I)   /*returns void*/
    {
        addBlackHoleAddrEdge(getValueNode(&I));
    }
    void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I)
    {
        addBlackHoleAddrEdge(getValueNode(&I));
    }
    void visitAtomicRMWInst(AtomicRMWInst &I)
    {
        addBlackHoleAddrEdge(getValueNode(&I));
    }

    /// Provide base case for our instruction visit.
    inline void visitInstruction(Instruction&)
    {
        // If a new instruction is added to LLVM that we don't handle.
        // TODO: ignore here:
    }
    //}@

};


} // end namespace SVF
#endif /* PAGGETTER_H_ */