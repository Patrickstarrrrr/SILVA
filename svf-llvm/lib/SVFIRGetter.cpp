#include "SVF-LLVM/SVFIRGetter.h"
#include "SVFIR/SVFModule.h"
#include "Util/SVFUtil.h"
#include "SVF-LLVM/BasicTypes.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "Util/CppUtil.h"
#include "SVFIR/SVFValue.h"
#include "SVFIR/PAGBuilderFromFile.h"
#include "SVF-LLVM/LLVMLoopAnalysis.h"
#include "Util/Options.h"
#include "SVF-LLVM/CHGBuilder.h"
#include "SVFIR/SVFFileSystem.h"
#include "SVF-LLVM/SymbolTableBuilder.h"


using namespace std;
using namespace SVF;
using namespace SVFUtil;
using namespace LLVMUtil;

std::unique_ptr<SVFIRGetter> SVFIRGetter::irGetter;

/*!
 * Return the object node offset according to GEP insn (V).
 * Given a gep edge p = q + i, if "i" is a constant then we return its offset size
 * otherwise if "i" is a variable determined by runtime, then it is a variant offset
 * Return TRUE if the offset of this GEP insn is a constant.
 */
bool SVFIRGetter::computeGepOffset(const User *V, AccessPath& ap)
{
    assert(V);

    const llvm::GEPOperator *gepOp = SVFUtil::dyn_cast<const llvm::GEPOperator>(V);
    DataLayout * dataLayout = getDataLayout(LLVMModuleSet::getLLVMModuleSet()->getMainLLVMModule());
    llvm::APInt byteOffset(dataLayout->getIndexSizeInBits(gepOp->getPointerAddressSpace()),0,true);
    if(gepOp && dataLayout && gepOp->accumulateConstantOffset(*dataLayout,byteOffset))
    {
        //s32_t bo = byteOffset.getSExtValue();
    }

    bool isConst = true;

    for (bridge_gep_iterator gi = bridge_gep_begin(*V), ge = bridge_gep_end(*V);
            gi != ge; ++gi)
    {
        const Type* gepTy = *gi;
        const SVFType* svfGepTy = LLVMModuleSet::getLLVMModuleSet()->getSVFType(gepTy);
        const Value* offsetVal = gi.getOperand();
        const SVFValue* offsetSvfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(offsetVal);
        assert(gepTy != offsetVal->getType() && "iteration and operand have the same type?");
        ap.addOffsetVarAndGepTypePair(getPAG()->getGNode(getPAG()->getValueNode(offsetSvfVal)), svfGepTy);

        //The int value of the current index operand
        const ConstantInt* op = SVFUtil::dyn_cast<ConstantInt>(offsetVal);

        // if Options::ModelConsts() is disabled. We will treat whole array as one,
        // but we can distinguish different field of an array of struct, e.g. s[1].f1 is different from s[0].f2
        if(const ArrayType* arrTy = SVFUtil::dyn_cast<ArrayType>(gepTy))
        {
            if(!op || (arrTy->getArrayNumElements() <= (u32_t)op->getSExtValue()))
                continue;
            APOffset idx = op->getSExtValue();
            u32_t offset = pag->getSymbolInfo()->getFlattenedElemIdx(LLVMModuleSet::getLLVMModuleSet()->getSVFType(arrTy), idx);
            ap.setFldIdx(ap.getConstantFieldIdx() + offset);
        }
        else if (const StructType *ST = SVFUtil::dyn_cast<StructType>(gepTy))
        {
            assert(op && "non-const offset accessing a struct");
            //The actual index
            APOffset idx = op->getSExtValue();
            u32_t offset = pag->getSymbolInfo()->getFlattenedElemIdx(LLVMModuleSet::getLLVMModuleSet()->getSVFType(ST), idx);
            ap.setFldIdx(ap.getConstantFieldIdx() + offset);
        }
        else if (gepTy->isSingleValueType())
        {
            // If it's a non-constant offset access
            // If its point-to target is struct or array, it's likely an array accessing (%result = gep %struct.A* %a, i32 %non-const-index)
            // If its point-to target is single value (pointer arithmetic), then it's a variant gep (%result = gep i8* %p, i32 %non-const-index)
            if(!op && gepTy->isPointerTy() && getPtrElementType(SVFUtil::dyn_cast<PointerType>(gepTy))->isSingleValueType())
                isConst = false;

            // The actual index
            //s32_t idx = op->getSExtValue();

            // For pointer arithmetic we ignore the byte offset
            // consider using inferFieldIdxFromByteOffset(geopOp,dataLayout,ap,idx)?
            // ap.setFldIdx(ap.getConstantFieldIdx() + inferFieldIdxFromByteOffset(geopOp,idx));
        }
    }
    return isConst;
}

/*!
 * Visit alloca instructions
 * Add edge V (dst) <-- O (src), V here is a value node on SVFIR, O is object node on SVFIR
 */
void SVFIRGetter::visitAllocaInst(AllocaInst &inst)
{

    // AllocaInst should always be a pointer type
    assert(SVFUtil::isa<PointerType>(inst.getType()));

    DBOUT(DPAGBuild, outs() << "process alloca  " << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&inst)->toString() << " \n");
    NodeID dst = getValueNode(&inst);

    NodeID src = getObjectNode(&inst);

    addAddrEdge(src, dst);

}

/*!
 * Visit phi instructions
 */
void SVFIRGetter::visitPHINode(PHINode &inst)
{

    DBOUT(DPAGBuild, outs() << "process phi " << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&inst)->toString() << "  \n");

    NodeID dst = getValueNode(&inst);

    for (u32_t i = 0; i < inst.getNumIncomingValues(); ++i)
    {
        const Value* val = inst.getIncomingValue(i);
        const Instruction* incomingInst = SVFUtil::dyn_cast<Instruction>(val);
        bool matched = (incomingInst == nullptr ||
                        incomingInst->getFunction() == inst.getFunction());
        (void) matched; // Suppress warning of unused variable under release build
        assert(matched && "incomingInst's Function incorrect");
        const Instruction* predInst = &inst.getIncomingBlock(i)->back();
        const SVFInstruction* svfPrevInst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(predInst);
        const ICFGNode* icfgNode = pag->getICFG()->getICFGNode(svfPrevInst);
        NodeID src = getValueNode(val);
        addPhiStmt(dst,src,icfgNode);
    }
}

/*
 * Visit load instructions
 */
void SVFIRGetter::visitLoadInst(LoadInst &inst)
{
    DBOUT(DPAGBuild, outs() << "process load  " << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&inst)->toString() << " \n");

    NodeID dst = getValueNode(&inst);

    NodeID src = getValueNode(inst.getPointerOperand());

    addLoadEdge(src, dst);
}

/*!
 * Visit store instructions
 */
void SVFIRGetter::visitStoreInst(StoreInst &inst)
{
    // StoreInst itself should always not be a pointer type
    assert(!SVFUtil::isa<PointerType>(inst.getType()));

    DBOUT(DPAGBuild, outs() << "process store " << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&inst)->toString() << " \n");

    NodeID dst = getValueNode(inst.getPointerOperand());

    NodeID src = getValueNode(inst.getValueOperand());

    addStoreEdge(src, dst);

}

/*!
 * Visit getelementptr instructions
 */
void SVFIRGetter::visitGetElementPtrInst(GetElementPtrInst &inst)
{

    NodeID dst = getValueNode(&inst);
    // GetElementPtrInst should always be a pointer or a vector contains pointers
    // for now we don't handle vector type here
    if(SVFUtil::isa<VectorType>(inst.getType()))
    {
        addBlackHoleAddrEdge(dst);
        return;
    }

    assert(SVFUtil::isa<PointerType>(inst.getType()));

    DBOUT(DPAGBuild, outs() << "process gep  " << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&inst)->toString() << " \n");

    NodeID src = getValueNode(inst.getPointerOperand());

    AccessPath ap;
    bool constGep = computeGepOffset(&inst, ap);
    addGepEdge(src, dst, ap, constGep);
}

/*
 * Visit cast instructions
 */
void SVFIRGetter::visitCastInst(CastInst &inst)
{

    DBOUT(DPAGBuild, outs() << "process cast  " << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&inst)->toString() << " \n");
    NodeID dst = getValueNode(&inst);

    if (SVFUtil::isa<IntToPtrInst>(&inst))
    {
        addBlackHoleAddrEdge(dst);
    }
    else
    {
        const Value* opnd = inst.getOperand(0);
        if (!SVFUtil::isa<PointerType>(opnd->getType()))
            opnd = stripAllCasts(opnd);

        NodeID src = getValueNode(opnd);
        addCopyEdge(src, dst);
    }
}

/*!
 * Visit Binary Operator
 */
void SVFIRGetter::visitBinaryOperator(BinaryOperator &inst)
{
    NodeID dst = getValueNode(&inst);
    assert(inst.getNumOperands() == 2 && "not two operands for BinaryOperator?");
    Value* op1 = inst.getOperand(0);
    NodeID op1Node = getValueNode(op1);
    Value* op2 = inst.getOperand(1);
    NodeID op2Node = getValueNode(op2);
    u32_t opcode = inst.getOpcode();
    addBinaryOPEdge(op1Node, op2Node, dst, opcode);
}

/*!
 * Visit Unary Operator
 */
void SVFIRGetter::visitUnaryOperator(UnaryOperator &inst)
{
    NodeID dst = getValueNode(&inst);
    assert(inst.getNumOperands() == 1 && "not one operand for Unary instruction?");
    Value* opnd = inst.getOperand(0);
    NodeID src = getValueNode(opnd);
    u32_t opcode = inst.getOpcode();
    addUnaryOPEdge(src, dst, opcode);
}

/*!
 * Visit compare instruction
 */
void SVFIRGetter::visitCmpInst(CmpInst &inst)
{
    NodeID dst = getValueNode(&inst);
    assert(inst.getNumOperands() == 2 && "not two operands for compare instruction?");
    Value* op1 = inst.getOperand(0);
    NodeID op1Node = getValueNode(op1);
    Value* op2 = inst.getOperand(1);
    NodeID op2Node = getValueNode(op2);
    u32_t predicate = inst.getPredicate();
    addCmpEdge(op1Node, op2Node, dst, predicate);
}


/*!
 * Visit select instructions
 */
void SVFIRGetter::visitSelectInst(SelectInst &inst)
{

    DBOUT(DPAGBuild, outs() << "process select  " << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&inst)->toString() << " \n");

    NodeID dst = getValueNode(&inst);
    NodeID src1 = getValueNode(inst.getTrueValue());
    NodeID src2 = getValueNode(inst.getFalseValue());
    NodeID cond = getValueNode(inst.getCondition());
    /// Two operands have same incoming basic block, both are the current BB
    addSelectStmt(dst,src1,src2, cond);
}

void SVFIRGetter::visitCallInst(CallInst &i)
{
    visitCallSite(&i);
}

void SVFIRGetter::visitInvokeInst(InvokeInst &i)
{
    visitCallSite(&i);
}

void SVFIRGetter::visitCallBrInst(CallBrInst &i)
{
    visitCallSite(&i);
}

/*
 * Visit callsites
 */
void SVFIRGetter::visitCallSite(CallBase* cs)
{

    // skip llvm intrinsics
    if(isIntrinsicInst(cs))
        return;

    const SVFInstruction* svfcall = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(cs);

    DBOUT(DPAGBuild,
          outs() << "process callsite " << svfcall->toString() << "\n");

    
    CallICFGNode* callBlockNode = pag->getICFG()->getCallICFGNode(svfcall);
    RetICFGNode* retBlockNode = pag->getICFG()->getRetICFGNode(svfcall);

    direCallsites.push_back(callBlockNode);
    // pag->addCallSite(callBlockNode);

    // /// Collect callsite arguments and returns
    // for (u32_t i = 0; i < cs->arg_size(); i++)
    //     pag->addCallSiteArgs(callBlockNode,pag->getGNode(getValueNode(cs->getArgOperand(i))));

    // if(!cs->getType()->isVoidTy())
    //     pag->addCallSiteRets(retBlockNode,pag->getGNode(getValueNode(cs)));

    if (const Function *callee = LLVMUtil::getCallee(cs))
    {
        callee = LLVMUtil::getDefFunForMultipleModule(callee);
        const SVFFunction* svfcallee = LLVMModuleSet::getLLVMModuleSet()->getSVFFunction(callee);
        if (isExtCall(svfcallee))
        {
            // handleExtCall(cs, svfcallee); todo: handleextcall_inc
        }
        else
        {
            handleDirectCall(cs, callee);
        }
    }
    else
    {
        //If the callee was not identified as a function (null F), this is indirect.
        handleIndCall(cs);
    }
}

/*!
 * Visit return instructions of a function
 */
void SVFIRGetter::visitReturnInst(ReturnInst &inst)
{

    // ReturnInst itself should always not be a pointer type
    assert(!SVFUtil::isa<PointerType>(inst.getType()));

    DBOUT(DPAGBuild, outs() << "process return  " << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&inst)->toString() << " \n");

    if(Value* src = inst.getReturnValue())
    {
        const SVFFunction *F = LLVMModuleSet::getLLVMModuleSet()->getSVFFunction(inst.getParent()->getParent());

        NodeID rnF = getReturnNode(F);
        NodeID vnS = getValueNode(src);
        const SVFInstruction* svfInst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(&inst);
        const ICFGNode* icfgNode = pag->getICFG()->getICFGNode(svfInst);
        //vnS may be null if src is a null ptr
        addPhiStmt(rnF,vnS,icfgNode);
    }
}

/*!
 * visit extract value instructions for structures in registers
 * TODO: for now we just assume the pointer after extraction points to blackhole
 * for example %24 = extractvalue { i32, %struct.s_hash* } %call34, 0
 * %24 is a pointer points to first field of a register value %call34
 * however we can not create %call34 as an memory object, as it is register value.
 * Is that necessary treat extract value as getelementptr instruction later to get more precise results?
 */
void SVFIRGetter::visitExtractValueInst(ExtractValueInst  &inst)
{
    NodeID dst = getValueNode(&inst);
    addBlackHoleAddrEdge(dst);
}

/*!
 * The �extractelement� instruction extracts a single scalar element from a vector at a specified index.
 * TODO: for now we just assume the pointer after extraction points to blackhole
 * The first operand of an �extractelement� instruction is a value of vector type.
 * The second operand is an index indicating the position from which to extract the element.
 *
 * <result> = extractelement <4 x i32> %vec, i32 0    ; yields i32
 */
void SVFIRGetter::visitExtractElementInst(ExtractElementInst &inst)
{
    NodeID dst = getValueNode(&inst);
    addBlackHoleAddrEdge(dst);
}

/*!
 * Branch and switch instructions are treated as UnaryOP
 * br %cmp label %if.then, label %if.else
 */
void SVFIRGetter::visitBranchInst(BranchInst &inst)
{
    NodeID brinst = getValueNode(&inst);
    NodeID cond;
    if (inst.isConditional())
        cond = getValueNode(inst.getCondition());
    else
        cond = pag->getNullPtr();

    assert(inst.getNumSuccessors() <= 2 && "if/else has more than two branches?");

    BranchStmt::SuccAndCondPairVec successors;
    for (u32_t i = 0; i < inst.getNumSuccessors(); ++i)
    {
        const Instruction* succInst = &inst.getSuccessor(i)->front();
        const SVFInstruction* svfSuccInst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(succInst);
        const ICFGNode* icfgNode = pag->getICFG()->getICFGNode(svfSuccInst);
        successors.push_back(std::make_pair(icfgNode, 1-i));
    }
    addBranchStmt(brinst, cond,successors);
}

void SVFIRGetter::visitSwitchInst(SwitchInst &inst)
{
    NodeID brinst = getValueNode(&inst);
    NodeID cond = getValueNode(inst.getCondition());

    BranchStmt::SuccAndCondPairVec successors;

    // get case successor basic block and related case value
    SuccBBAndCondValPairVec succBB2CondValPairVec;
    LLVMUtil::getSuccBBandCondValPairVec(inst, succBB2CondValPairVec);
    for (auto &succBB2CaseValue : succBB2CondValPairVec)
    {
        s64_t val = LLVMUtil::getCaseValue(inst, succBB2CaseValue);
        const BasicBlock *succBB = succBB2CaseValue.first;
        const Instruction* succInst = &succBB->front();
        const SVFInstruction* svfSuccInst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(succInst);
        const ICFGNode* icfgNode = pag->getICFG()->getICFGNode(svfSuccInst);
        successors.push_back(std::make_pair(icfgNode, val));
    }
    addBranchStmt(brinst, cond, successors);
}

///   %ap = alloca %struct.va_list
///  %ap2 = bitcast %struct.va_list* %ap to i8*
/// ; Read a single integer argument from %ap2
/// %tmp = va_arg i8* %ap2, i32 (VAArgInst)
/// TODO: for now, create a copy edge from %ap2 to %tmp, we assume here %tmp should point to the n-th argument of the var_args
void SVFIRGetter::visitVAArgInst(VAArgInst &inst)
{
    NodeID dst = getValueNode(&inst);
    Value* opnd = inst.getPointerOperand();
    NodeID src = getValueNode(opnd);
    addCopyEdge(src,dst);
}

/// <result> = freeze ty <val>
/// If <val> is undef or poison, ‘freeze’ returns an arbitrary, but fixed value of type `ty`
/// Otherwise, this instruction is a no-op and returns the input <val>
/// For now, we assume <val> is never a poison or undef.
void SVFIRGetter::visitFreezeInst(FreezeInst &inst)
{
    NodeID dst = getValueNode(&inst);
    for (u32_t i = 0; i < inst.getNumOperands(); i++)
    {
        Value* opnd = inst.getOperand(i);
        NodeID src = getValueNode(opnd);
        addCopyEdge(src,dst);
    }
}

/*!
 * Add the constraints for a direct, non-external call.
 */
void SVFIRGetter::handleDirectCall(CallBase* cs, const Function *F)
{

    assert(F);
    const SVFInstruction* svfcall = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(cs);
    const SVFFunction* svffun = LLVMModuleSet::getLLVMModuleSet()->getSVFFunction(F);
    DBOUT(DPAGBuild,
          outs() << "handle direct call " << svfcall->toString() << " callee " << F->getName().str() << "\n");

    //Only handle the ret.val. if it's used as a ptr.
    NodeID dstrec = getValueNode(cs);
    //Does it actually return a ptr?
    if (!cs->getType()->isVoidTy())
    {
        NodeID srcret = getReturnNode(svffun);
        CallICFGNode* callICFGNode = pag->getICFG()->getCallICFGNode(svfcall);
        FunExitICFGNode* exitICFGNode = pag->getICFG()->getFunExitICFGNode(svffun);
        addRetEdge(srcret, dstrec,callICFGNode, exitICFGNode);
    }
    //Iterators for the actual and formal parameters
    u32_t itA = 0, ieA = cs->arg_size();
    Function::const_arg_iterator itF = F->arg_begin(), ieF = F->arg_end();
    //Go through the fixed parameters.
    DBOUT(DPAGBuild, outs() << "      args:");
    for (; itF != ieF; ++itA, ++itF)
    {
        //Some programs (e.g. Linux kernel) leave unneeded parameters empty.
        if (itA == ieA)
        {
            DBOUT(DPAGBuild, outs() << " !! not enough args\n");
            break;
        }
        const Value* AA = cs->getArgOperand(itA), *FA = &*itF; //current actual/formal arg

        DBOUT(DPAGBuild, outs() << "process actual parm  " << LLVMModuleSet::getLLVMModuleSet()->getSVFValue(AA)->toString() << " \n");

        NodeID dstFA = getValueNode(FA);
        NodeID srcAA = getValueNode(AA);
        CallICFGNode* icfgNode = pag->getICFG()->getCallICFGNode(svfcall);
        FunEntryICFGNode* entry = pag->getICFG()->getFunEntryICFGNode(svffun);
        addCallEdge(srcAA, dstFA, icfgNode, entry);
    }
    //Any remaining actual args must be varargs.
    if (F->isVarArg())
    {
        NodeID vaF = getVarargNode(svffun);
        DBOUT(DPAGBuild, outs() << "\n      varargs:");
        for (; itA != ieA; ++itA)
        {
            const Value* AA = cs->getArgOperand(itA);
            NodeID vnAA = getValueNode(AA);
            CallICFGNode* icfgNode = pag->getICFG()->getCallICFGNode(svfcall);
            FunEntryICFGNode* entry = pag->getICFG()->getFunEntryICFGNode(svffun);
            addCallEdge(vnAA,vaF, icfgNode,entry);
        }
    }
    if(itA != ieA)
    {
        /// FIXME: this assertion should be placed for correct checking except
        /// bug program like 188.ammp, 300.twolf
        writeWrnMsg("too many args to non-vararg func.");
        writeWrnMsg("(" + svfcall->getSourceLoc() + ")");

    }
}

/*!
 * Indirect call is resolved on-the-fly during pointer analysis
 */
void SVFIRGetter::handleIndCall(CallBase* cs)
{
    const SVFInstruction* svfcall = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(cs);
    const SVFValue* svfcalledval = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(cs->getCalledOperand());

    const CallICFGNode* cbn = pag->getICFG()->getCallICFGNode(svfcall);
    indireCallsites.push_back(cbn);
    // pag->addIndirectCallsites(cbn,pag->getValueNode(svfcalledval));
    // TODO: Mark diff callsite here? -- wjy
}


/*!
 * Add a temp field value node according to base value and offset
 * this node is after the initial node method, it is out of scope of symInfo table
 */
NodeID SVFIRGetter::getGepValVar(const Value* val, const AccessPath& ap, const SVFType* elementType)
{
    NodeID base = pag->getBaseValVar(getValueNode(val));
    NodeID gepval = pag->getGepValVar(curVal, base, ap);
    if (gepval==UINT_MAX)
    {
        assert(0 && "getGepVal failed!!");
    }
    return gepval;      
}


/*!
 * Add the load/store constraints and temp. nodes for the complex constraint
 * *D = *S (where D/S may point to structs).
 */
void SVFIRGetter::addComplexConsForExt(Value *D, Value *S, const Value* szValue)
{
    assert(D && S);
    NodeID vnD= getValueNode(D), vnS= getValueNode(S);
    if(!vnD || !vnS)
        return;

    std::vector<AccessPath> fields;

    //Get the max possible size of the copy, unless it was provided.
    std::vector<AccessPath> srcFields;
    std::vector<AccessPath> dstFields;
    const Type* stype = getBaseTypeAndFlattenedFields(S, srcFields, szValue);
    const Type* dtype = getBaseTypeAndFlattenedFields(D, dstFields, szValue);
    if(srcFields.size() > dstFields.size())
        fields = dstFields;
    else
        fields = srcFields;

    /// If sz is 0, we will add edges for all fields.
    u32_t sz = fields.size();

    if (fields.size() == 1 && (LLVMUtil::isConstDataOrAggData(D) || LLVMUtil::isConstDataOrAggData(S)))
    {
        // TODO: getdummy -- wjy
        // NodeID dummy = pag->addDummyValNode();
        // addLoadEdge(vnD,dummy);
        // addStoreEdge(dummy,vnS);
        return;
    }

    //For each field (i), add (Ti = *S + i) and (*D + i = Ti).
    for (u32_t index = 0; index < sz; index++)
    {
        // TODO: getdummy -- wjy
        // LLVMModuleSet* llvmmodule = LLVMModuleSet::getLLVMModuleSet();
        // const SVFType* dElementType = pag->getSymbolInfo()->getFlatternedElemType(llvmmodule->getSVFType(dtype),
        //                               fields[index].getConstantFieldIdx());
        // const SVFType* sElementType = pag->getSymbolInfo()->getFlatternedElemType(llvmmodule->getSVFType(stype),
        //                               fields[index].getConstantFieldIdx());
        // NodeID dField = getGepValVar(D,fields[index],dElementType);
        // NodeID sField = getGepValVar(S,fields[index],sElementType);
        // NodeID dummy = pag->addDummyValNode();
        // addLoadEdge(sField,dummy);
        // addStoreEdge(dummy,dField);
    }
}

void SVFIRGetter::handleExtCall(const CallBase* cs, const SVFFunction* svfCallee)
{
    const SVFInstruction* svfInst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(cs);
    const SVFCallInst* svfCall = SVFUtil::cast<SVFCallInst>(svfInst);

    if (isHeapAllocExtCallViaRet(svfCall))
    {
        NodeID val = pag->getValueNode(svfInst);
        NodeID obj = pag->getObjectNode(svfInst);
        addAddrEdge(obj, val);
    }
    else if (isHeapAllocExtCallViaArg(svfCall))
    {
        u32_t arg_pos = getHeapAllocHoldingArgPosition(svfCallee);
        const SVFValue* arg = svfCall->getArgOperand(arg_pos);
        if (arg->getType()->isPointerTy())
        {
            // TODO: getdummy -- wjy
            // NodeID vnArg = pag->getValueNode(arg);
            // NodeID dummy = pag->addDummyValNode();
            // NodeID obj = pag->addDummyObjNode(arg->getType());
            // if (vnArg && dummy && obj)
            // {
            //     addAddrEdge(obj, dummy);
            //     addStoreEdge(dummy, vnArg);
            // }
        }
        else
        {
            writeWrnMsg("Arg receiving new object must be pointer type");
        }
    }
    else if (isMemcpyExtFun(svfCallee))
    {
        // Side-effects similar to void *memcpy(void *dest, const void * src, size_t n)
        // which  copies n characters from memory area 'src' to memory area 'dest'.
        if(svfCallee->getName().find("iconv") != std::string::npos)
            addComplexConsForExt(cs->getArgOperand(3), cs->getArgOperand(1), nullptr);
        else if(svfCallee->getName().find("bcopy") != std::string::npos)
            addComplexConsForExt(cs->getArgOperand(1), cs->getArgOperand(0), cs->getArgOperand(2));
        if(svfCall->arg_size() == 3)
            addComplexConsForExt(cs->getArgOperand(0), cs->getArgOperand(1), cs->getArgOperand(2));
        else
            addComplexConsForExt(cs->getArgOperand(0), cs->getArgOperand(1), nullptr);
        if(SVFUtil::isa<PointerType>(cs->getType()))
            addCopyEdge(getValueNode(cs->getArgOperand(0)), getValueNode(cs));
    }
    else if(isMemsetExtFun(svfCallee))
    {
        // Side-effects similar to memset(void *str, int c, size_t n)
        // which copies the character c (an unsigned char) to the first n characters of the string pointed to, by the argument str
        std::vector<AccessPath> dstFields;
        const Type *dtype = getBaseTypeAndFlattenedFields(cs->getArgOperand(0), dstFields, cs->getArgOperand(2));
        u32_t sz = dstFields.size();
        //For each field (i), add store edge *(arg0 + i) = arg1
        for (u32_t index = 0; index < sz; index++)
        {
            LLVMModuleSet* llvmmodule = LLVMModuleSet::getLLVMModuleSet();
            const SVFType* dElementType = pag->getSymbolInfo()->getFlatternedElemType(llvmmodule->getSVFType(dtype), dstFields[index].getConstantFieldIdx());
            NodeID dField = getGepValVar(cs->getArgOperand(0), dstFields[index], dElementType);
            addStoreEdge(getValueNode(cs->getArgOperand(1)),dField);
        }
        if(SVFUtil::isa<PointerType>(cs->getType()))
            addCopyEdge(getValueNode(cs->getArgOperand(0)), getValueNode(cs));
    }
    else if(svfCallee->getName().compare("dlsym") == 0)
    {
        /*
        Side-effects of void* dlsym( void* handle, const char* funName),
        Locate the function with the name "funName," then add a "copy" edge between the callsite and that function.
        dlsym() example:
            int main() {
                // Open the shared library
                void* handle = dlopen("./my_shared_library.so", RTLD_LAZY);
                // Find the function address
                void (*myFunctionPtr)() = (void (*)())dlsym(handle, "myFunction");
                // Call the function
                myFunctionPtr();
            }
        */
        const Value* src = cs->getArgOperand(1);
        if(const GetElementPtrInst* gep = SVFUtil::dyn_cast<GetElementPtrInst>(src))
            src = stripConstantCasts(gep->getPointerOperand());

        auto getHookFn = [](const Value* src)->const Function*
        {
            if (!SVFUtil::isa<GlobalVariable>(src))
                return nullptr;

            auto *glob = SVFUtil::cast<GlobalVariable>(src);
            if (!glob->hasInitializer() || !SVFUtil::isa<ConstantDataArray>(glob->getInitializer()))
                return nullptr;

            auto *constarray = SVFUtil::cast<ConstantDataArray>(glob->getInitializer());
            return LLVMUtil::getProgFunction(constarray->getAsCString().str());
        };

        if (const Function *fn = getHookFn(src))
        {
            NodeID srcNode = getValueNode(fn);
            addCopyEdge(srcNode,  getValueNode(cs));
        }
    }
    else if(svfCallee->getName().find("_ZSt29_Rb_tree_insert_and_rebalancebPSt18_Rb_tree_node_baseS0_RS_") != std::string::npos)
    {
        // The purpose of this function is to insert a new node into the red-black tree and then rebalance the tree to ensure that the red-black tree properties are maintained.
        assert(svfCall->arg_size() == 4 && "_Rb_tree_insert_and_rebalance should have 4 arguments.\n");

        // We have vArg3 points to the entry of _Rb_tree_node_base { color; parent; left; right; }.
        // Now we calculate the offset from base to vArg3
        NodeID vnArg3 = pag->getValueNode(svfCall->getArgOperand(3));
        APOffset offset = getAccessPathFromBaseNode(vnArg3).getConstantFieldIdx();

        // We get all flattened fields of base
        vector<AccessPath> fields =  pag->getTypeLocSetsMap(vnArg3).second;

        // We summarize the side effects: arg3->parent = arg1, arg3->left = arg1, arg3->right = arg1
        // Note that arg0 is aligned with "offset".
        for (APOffset i = offset + 1; i <= offset + 3; ++i)
        {
            if((u32_t)i >= fields.size())
                break;
            const SVFType* elementType = pag->getSymbolInfo()->getFlatternedElemType(pag->getTypeLocSetsMap(vnArg3).first,
                                         fields[i].getConstantFieldIdx());
            NodeID vnD = getGepValVar(cs->getArgOperand(3), fields[i], elementType);
            NodeID vnS = pag->getValueNode(svfCall->getArgOperand(1));
            if(vnD && vnS)
                addStoreEdge(vnS,vnD);
        }
    }

    if (isThreadForkCall(svfInst))
    {
        if (const SVFFunction* forkedFun = SVFUtil::dyn_cast<SVFFunction>(getForkedFun(svfInst)))
        {
            forkedFun = forkedFun->getDefFunForMultipleModule();
            const SVFValue* actualParm = getActualParmAtForkSite(svfInst);
            /// pthread_create has 1 arg.
            /// apr_thread_create has 2 arg.
            assert((forkedFun->arg_size() <= 2) && "Size of formal parameter of start routine should be one");
            if (forkedFun->arg_size() <= 2 && forkedFun->arg_size() >= 1)
            {
                const SVFArgument* formalParm = forkedFun->getArg(0);
                /// Connect actual parameter to formal parameter of the start routine
                if (actualParm->getType()->isPointerTy() && formalParm->getType()->isPointerTy())
                {
                    CallICFGNode *icfgNode = pag->getICFG()->getCallICFGNode(svfInst);
                    FunEntryICFGNode *entry = pag->getICFG()->getFunEntryICFGNode(forkedFun);
                    addThreadForkEdge(pag->getValueNode(actualParm), pag->getValueNode(formalParm), icfgNode, entry);
                }
            }
        }
        else
        {
            /// handle indirect calls at pthread create APIs e.g., pthread_create(&t1, nullptr, fp, ...);
            /// const Value* fun = ThreadAPI::getThreadAPI()->getForkedFun(inst);
            /// if(!SVFUtil::isa<Function>(fun))
            ///    pag->addIndirectCallsites(cs,pag->getValueNode(fun));
        }
        /// If forkedFun does not pass to spawnee as function type but as void pointer
        /// remember to update inter-procedural callgraph/SVFIR/SVFG etc. when indirect call targets are resolved
        /// We don't connect the callgraph here, further investigation is need to handle mod-ref during SVFG construction.
    }

    /// create inter-procedural SVFIR edges for hare_parallel_for calls
    else if (isHareParForCall(svfInst))
    {
        if (const SVFFunction* taskFunc = SVFUtil::dyn_cast<SVFFunction>(getTaskFuncAtHareParForSite(svfInst)))
        {
            /// The task function of hare_parallel_for has 3 args.
            assert((taskFunc->arg_size() == 3) && "Size of formal parameter of hare_parallel_for's task routine should be 3");
            const SVFValue* actualParm = getTaskDataAtHareParForSite(svfInst);
            const SVFArgument* formalParm = taskFunc->getArg(0);
            /// Connect actual parameter to formal parameter of the start routine
            if (actualParm->getType()->isPointerTy() && formalParm->getType()->isPointerTy())
            {
                CallICFGNode *icfgNode = pag->getICFG()->getCallICFGNode(svfInst);
                FunEntryICFGNode *entry = pag->getICFG()->getFunEntryICFGNode(taskFunc);
                addThreadForkEdge(pag->getValueNode(actualParm), pag->getValueNode(formalParm), icfgNode, entry);
            }
        }
        else
        {
            /// handle indirect calls at hare_parallel_for (e.g., hare_parallel_for(..., fp, ...);
            /// const Value* fun = ThreadAPI::getThreadAPI()->getForkedFun(inst);
            /// if(!SVFUtil::isa<Function>(fun))
            ///    pag->addIndirectCallsites(cs,pag->getValueNode(fun));
        }
    }

    /// TODO: inter-procedural SVFIR edges for thread joins
}


/*!
 * Find the base type and the max possible offset of an object pointed to by (V).
 */
const Type* SVFIRGetter::getBaseTypeAndFlattenedFields(const Value* V, std::vector<AccessPath> &fields, const Value* szValue)
{
    assert(V);
    const Value* value = getBaseValueForExtArg(V);
    const Type* T = value->getType();
    while (const PointerType *ptype = SVFUtil::dyn_cast<PointerType>(T))
        T = getPtrElementType(ptype);

    u32_t numOfElems = pag->getSymbolInfo()->getNumOfFlattenElements(LLVMModuleSet::getLLVMModuleSet()->getSVFType(T));
    /// use user-specified size for this copy operation if the size is a constaint int
    if(szValue && SVFUtil::isa<ConstantInt>(szValue))
    {
        numOfElems = (numOfElems > SVFUtil::cast<ConstantInt>(szValue)->getSExtValue()) ? SVFUtil::cast<ConstantInt>(szValue)->getSExtValue() : numOfElems;
    }

    LLVMContext& context = LLVMModuleSet::getLLVMModuleSet()->getContext();
    for(u32_t ei = 0; ei < numOfElems; ei++)
    {
        AccessPath ls(ei);
        // make a ConstantInt and create char for the content type due to byte-wise copy
        const ConstantInt* offset = ConstantInt::get(context, llvm::APInt(32, ei));
        const SVFValue* svfOffset = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(offset);
        // if (!pag->getSymbolInfo()->hasValSym(svfOffset))
        // {
        //     SymbolTableBuilder builder(pag->getSymbolInfo());
        //     builder.collectSym(offset);
        //     pag->addValNode(svfOffset, pag->getSymbolInfo()->getValSym(svfOffset));
        // }
        ls.addOffsetVarAndGepTypePair(getPAG()->getGNode(getPAG()->getValueNode(svfOffset)), nullptr);
        fields.push_back(ls);
    }
    return T;
}

/*!
 * Get a base SVFVar given a pointer
 * Return the source node of its connected normal gep edge
 * Otherwise return the node id itself
 * s32_t offset : gep offset
 */
AccessPath SVFIRGetter::getAccessPathFromBaseNode(NodeID nodeId)
{
    SVFVar* node  = pag->getGNode(nodeId);
    SVFStmt::SVFStmtSetTy& geps = node->getIncomingEdges(SVFStmt::Gep);
    /// if this node is already a base node
    if(geps.empty())
        return AccessPath(0);

    assert(geps.size()==1 && "one node can only be connected by at most one gep edge!");
    SVFVar::iterator it = geps.begin();
    const GepStmt* gepEdge = SVFUtil::cast<GepStmt>(*it);
    if(gepEdge->isVariantFieldGep())
        return AccessPath(0);
    else
        return gepEdge->getAccessPath();
}

const Value* SVFIRGetter::getBaseValueForExtArg(const Value* V)
{
    const Value*  value = stripAllCasts(V);
    assert(value && "null ptr?");
    if(const GetElementPtrInst* gep = SVFUtil::dyn_cast<GetElementPtrInst>(value))
    {
        APOffset totalidx = 0;
        for (bridge_gep_iterator gi = bridge_gep_begin(gep), ge = bridge_gep_end(gep); gi != ge; ++gi)
        {
            if(const ConstantInt* op = SVFUtil::dyn_cast<ConstantInt>(gi.getOperand()))
                totalidx += op->getSExtValue();
        }
        if(totalidx == 0 && !SVFUtil::isa<StructType>(value->getType()))
            value = gep->getPointerOperand();
    }

    // if the argument of memcpy is the result of an allocation (1) or a casted load instruction (2),
    // further steps are necessary to find the correct base value
    //
    // (1)
    // %call   = malloc 80
    // %0      = bitcast i8* %call to %struct.A*
    // %1      = bitcast %struct.B* %param to i8*
    // call void memcpy(%call, %1, 80)
    //
    // (2)
    // %0 = bitcast %struct.A* %param to i8*
    // %2 = bitcast %struct.B** %arrayidx to i8**
    // %3 = load i8*, i8** %2
    // call void @memcpy(%0, %3, 80)
    LLVMContext &cxt = LLVMModuleSet::getLLVMModuleSet()->getContext();
    if (value->getType() == PointerType::getInt8PtrTy(cxt))
    {
        // (1)
        if (const CallBase* cb = SVFUtil::dyn_cast<CallBase>(value))
        {
            const SVFInstruction* svfInst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(cb);
            if (SVFUtil::isHeapAllocExtCallViaRet(svfInst))
            {
                if (const Value* bitCast = getUniqueUseViaCastInst(cb))
                    return bitCast;
            }
        }
        // (2)
        else if (const LoadInst* load = SVFUtil::dyn_cast<LoadInst>(value))
        {
            if (const BitCastInst* bitCast = SVFUtil::dyn_cast<BitCastInst>(load->getPointerOperand()))
                return bitCast->getOperand(0);
        }
    }

    return value;
}
