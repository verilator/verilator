#include "V3PchAstNoMT.h"

#include "V3Quadstate.h"

#include <map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class QuadstateTypeReducerVisitor final : public VNVisitor {
    std::map<const AstNodeDType*, AstNodeDType*> m_typesToReduced;

    AstNodeDType* reduceTypeToTwoStateLogic(AstNodeDType* dtypep) {
        if (!dtypep) return nullptr;
        // FIXME: this is terrible since we call this for each Expr and this function in almost
        // each extp travels a whole subtree
        dtypep = dtypep->skipRefp();
        const auto it = m_typesToReduced.find(dtypep);
        if (it != m_typesToReduced.end()) return it->second;
        if (const AstBasicDType* const basicDtypep = VN_CAST(dtypep, BasicDType)) {
            if (!basicDtypep->isFourstate()) return dtypep;
            switch (basicDtypep->keyword()) {
            case VBasicDTypeKwd::LOGIC:
            case VBasicDTypeKwd::LOGIC_IMPLICIT:
                return basicDtypep->findBitDType(basicDtypep->width(), basicDtypep->widthMin(),
                                                 basicDtypep->numeric());
            case VBasicDTypeKwd::INTEGER: return basicDtypep->findIntDType();
            case VBasicDTypeKwd::TIME: return basicDtypep->findUInt64DType();
            default:
                basicDtypep->v3fatalSrc(
                    "Unhandled four state variable type: " << basicDtypep->keyword().ascii());
            }
        }
        if (AstNodeArrayDType* const arrayDtypep = VN_CAST(dtypep, NodeArrayDType)) {
            AstNodeArrayDType* const newp = arrayDtypep->cloneTree(false);
            newp->refDTypep(reduceTypeToTwoStateLogic(arrayDtypep->subDTypep()));
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_typesToReduced.insert({dtypep, newp});
            return newp;
        }
        if (AstDynArrayDType* const arrayDtypep = VN_CAST(dtypep, DynArrayDType)) {
            AstDynArrayDType* const newp = arrayDtypep->cloneTree(false);
            newp->refDTypep(reduceTypeToTwoStateLogic(arrayDtypep->subDTypep()));
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_typesToReduced.insert({dtypep, newp});
            return newp;
        }
        if (AstWildcardArrayDType* const arrayDtypep = VN_CAST(dtypep, WildcardArrayDType)) {
            AstWildcardArrayDType* const newp = arrayDtypep->cloneTree(false);
            newp->refDTypep(reduceTypeToTwoStateLogic(arrayDtypep->subDTypep()));
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_typesToReduced.insert({dtypep, newp});
            return newp;
        }
        if (AstSampleQueueDType* const queueDtypep = VN_CAST(dtypep, SampleQueueDType)) {
            AstSampleQueueDType* const newp = queueDtypep->cloneTree(false);
            newp->refDTypep(reduceTypeToTwoStateLogic(queueDtypep->subDTypep()));
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_typesToReduced.insert({dtypep, newp});
            return newp;
        }
        if (AstQueueDType* const queueDtypep = VN_CAST(dtypep, QueueDType)) {
            AstQueueDType* const newp = queueDtypep->cloneTree(false);
            newp->refDTypep(reduceTypeToTwoStateLogic(queueDtypep->subDTypep()));
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_typesToReduced.insert({dtypep, newp});
            return newp;
        }
        if (AstNodeUOrStructDType* const structDtypep = VN_CAST(dtypep, NodeUOrStructDType)) {
            AstNodeUOrStructDType* const newp = structDtypep->cloneTree(false);
            for (AstMemberDType* memberp = newp->membersp(); memberp;
                 memberp = VN_AS(memberp->nextp(), MemberDType)) {
                AstNodeDType* const newMemberDTypep
                    = reduceTypeToTwoStateLogic(memberp->subDTypep());
                memberp->refDTypep(newMemberDTypep);
                memberp->dtypep(newMemberDTypep);
            }
            newp->isFourstate(false);  // FIXME: allow four_state pragma in structs
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_typesToReduced.insert({dtypep, newp});
            return newp;
        }
        if (AstAssocArrayDType* const arrayDtypep = VN_CAST(dtypep, AssocArrayDType)) {
            AstAssocArrayDType* const newp = arrayDtypep->cloneTree(false);
            newp->refDTypep(reduceTypeToTwoStateLogic(arrayDtypep->subDTypep()));
            newp->keyDTypep(reduceTypeToTwoStateLogic(arrayDtypep->keyDTypep()));
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_typesToReduced.insert({dtypep, newp});
            return newp;
        }
        if (VN_IS(dtypep, VoidDType) || VN_IS(dtypep, ClassRefDType)
            || VN_IS(dtypep, IfaceRefDType) || VN_IS(dtypep, NBACommitQueueDType)
            || VN_IS(dtypep, CDType)) {
            return dtypep;
        }
        dtypep->v3fatalSrc("Unhandled DType: " << dtypep);
    }

    void visit(AstVar* const nodep) override {
        if (!nodep->attrFourState()) nodep->dtypep(reduceTypeToTwoStateLogic(nodep->dtypep()));
    }
    void visit(AstNodeExpr* const nodep) override {
        iterateChildren(nodep);
        if (!nodep->isFourState()) nodep->dtypep(reduceTypeToTwoStateLogic(nodep->dtypep()));
    }
    void visit(AstConsPackUOrStruct* const nodep) override {
        if (!nodep->isFourState()) {
            nodep->dtypep(reduceTypeToTwoStateLogic(nodep->dtypep()));
            AstMemberDType* dtypep = VN_AS(nodep->dtypep(), NodeUOrStructDType)->membersp();
            for (AstConsPackMember* memberp = nodep->membersp(); memberp;
                 memberp = VN_AS(memberp->nextp(), ConsPackMember)) {
                memberp->dtypep(dtypep);
                dtypep = VN_AS(dtypep->nextp(), MemberDType);
                iterateChildren(memberp);
            }
        }
    }
    void visit(AstNodeAssign* const nodep) override {
        iterateChildren(nodep);
        nodep->dtypep(nodep->lhsp()->dtypep());
    }
    void visit(AstConsPackMember* const nodep) override {
        nodep->v3fatalSrc("This node shall never be visited here");
    }
    void visit(AstNode* const nodep) override { iterateChildren(nodep); }

public:
    explicit QuadstateTypeReducerVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~QuadstateTypeReducerVisitor() override = default;
};

class QuadstateVisitor final : public VNVisitor {

    // AstNodeVarRef::user1()   -> bool whether it has been visited

    VNUser1InUse m_user1;

    std::map<const AstVar*, std::vector<AstAssignW*>> m_assignWToTrior;
    std::map<const AstVar*, std::vector<AstAssignW*>> m_assignWToTriand;
    std::map<const AstVar*, std::vector<AstAssignW*>> m_assignWToWire;
    bool m_expectFourStateExpr = false;
    bool m_isUnderExprp = false;

    bool expectsFourStateExpr() const { return m_expectFourStateExpr; }

    static AstNodeExpr* buildTree(std::vector<AstNodeExpr*> exprps, const VCFunc reductor) {
        while (exprps.size() > 1) {
            const size_t halfSize = exprps.size() / 2;
            for (size_t i = 0; i < halfSize; ++i) {
                AstNodeDType* const dtypep = exprps[i]->dtypep();
                exprps[i] = new AstCFuncHard{exprps[i]->fileline(), reductor,
                                             exprps[i]->addNext(exprps.back())};
                exprps[i]->dtypep(dtypep);
                exprps.pop_back();
            }
        }
        return exprps[0];
    }

    static void
    triorTriandReduce(const std::map<const AstVar*, std::vector<AstAssignW*>>& assignWs,
                      const VCFunc reductor) {
        for (const auto& pair : assignWs) {
            const std::vector<AstAssignW*>& assignps = pair.second;
            if (assignps.size() < 2) continue;
            std::vector<AstNodeExpr*> exprp;
            exprp.reserve(assignps.size());
            for (AstAssignW* const assignp : assignps) {
                exprp.push_back(assignp->rhsp()->unlinkFrBack());
            }
            assignps[0]->rhsp(buildTree(std::move(exprp), reductor));
            for (size_t i = 1; i < assignps.size(); ++i) {
                assignps[i]->unlinkFrBack()->deleteTree();
            }
        }
    }

    static bool hasAttrFourState(const AstNodeExpr* const exprp) {
        return v3Global.opt.fourstate() || exprp->exists([](const AstVarRef* const varRefp) {
            return varRefp->varp()->attrFourState();
        }) || (v3Global.opt.fourstateLiterals() && exprp->exists([](const AstConst* const nodep) {
                   return nodep->isFourState();
               }));
    }

    static AstNodeDType* fourStateTypeFromTwoState(const AstNodeDType* const nodep) {
        if (const AstBasicDType* const basicDTypep = VN_CAST(nodep, BasicDType)) {
            switch (basicDTypep->keyword()) {
            case VBasicDTypeKwd::BIT:
                return nodep->findLogicDType(basicDTypep->width(), basicDTypep->widthMin(),
                                             basicDTypep->numeric());
            case VBasicDTypeKwd::INT: return nodep->findSigned32DType();
            default:
                nodep->v3fatalSrc("Unsupported Basic 2-state type promotion to 4-state - "
                                  << basicDTypep->keyword().ascii());
            }
        }
        nodep->v3warn(E_UNSUPPORTED, "Unsupported 2-state type promotion to 4-state - " << nodep);
        return nullptr;
    }

    static AstCFuncHard* wrapExprpInCFuncHard(AstNodeExpr* const exprp, const VCFunc func) {
        VNRelinker relinker;
        exprp->unlinkFrBack(&relinker);
        AstCFuncHard* const newp = new AstCFuncHard{exprp->fileline(), func, exprp};
        relinker.relink(newp);
        return newp;
    }

    static void castFourToTwo(AstNodeExpr* const exprp) {
        if (!exprp->dtypep()->isFourstate()) return;
        if (const AstConst* const constp = VN_CAST(exprp, Const)) {
            if (!constp->num().isAnyXZ()) return;
        }
        // if (AstCFuncHard* const cfuncHard = VN_CAST(exprp, CFuncHard)) {  // FIXME
        //     if (cfuncHard->cfunc() == VCFunc::FOUR_STATE_FROM_TWO_STATE) {
        //         VNRelinker relinker;
        //         exprp->unlinkFrBack(&relinker);
        //         relinker.relink(cfuncHard->pinsp()->unlinkFrBack());
        //         cfuncHard->deleteTree();
        //         return;
        //     }
        // }
        VNRelinker relinker;
        exprp->unlinkFrBack(&relinker);
        AstCCast* const newp = new AstCCast{exprp->fileline(), exprp, exprp};
        relinker.relink(newp);
        newp->dtypeSetLogicUnsized(exprp->dtypep()->width(), exprp->dtypep()->widthMin(),
                                   exprp->dtypep()->numeric());
    }

    static void castTwoToFour(AstNodeExpr* const exprp) {
        if (exprp->dtypep()->isFourstate()) return;
        // Casting from four to two and back has some side effects e.g.: x becomes 0
        VNRelinker relinker;
        exprp->unlinkFrBack(&relinker);
        relinker.relink(
            new AstCCast{exprp->fileline(), exprp, fourStateTypeFromTwoState(exprp->dtypep())});
    }

    void visit(AstNodeAssign* const nodep) override {
        VL_RESTORER(m_expectFourStateExpr);
        if (const AstVarRef* const varRefp = VN_CAST(nodep->lhsp(), VarRef)) {
            m_expectFourStateExpr = varRefp->varp()->attrFourState();
            if (AstAssignW* const assignWp = VN_CAST(nodep, AssignW)) {
                const AstVar* const varp = varRefp->varp();
                if (varp->attrFourState()) {
                    switch (varp->varType()) {
                    case VVarType::TRIOR: m_assignWToTrior[varp].push_back(assignWp); break;
                    case VVarType::TRIAND: m_assignWToTriand[varp].push_back(assignWp); break;
                    case VVarType::TRIWIRE:
                    case VVarType::WIRE: m_assignWToWire[varp].push_back(assignWp); break;
                    default: break;
                    }
                }
            }
        } else if (nodep->lhsp()->isFourState()) {
            nodep->v3warn(EC_INFO,
                          "assign with complex lhs is unsupported in 4-state logic context");
        }
        iterateChildren(nodep);
        // if (!expectsFourStateExpr()
        //     && nodep->rhsp()->isFourState()) {  // FIXME check dtype which will be faster
        //     wrapExprpInCFuncHard(nodep->rhsp(), VCFunc::FOUR_STATE_TWO_STATE_VALUE)
        //         ->dtypep(nodep->lhsp()->dtypep());  // FIXME What if there is a width mismatch
        // }
    }
    void visit(AstNodeIf* const nodep) override {
        {
            VL_RESTORER(m_expectFourStateExpr);
            m_expectFourStateExpr = hasAttrFourState(nodep->condp());
            iterateAndNextNull(nodep->condp());
            if (expectsFourStateExpr()) {
                wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
            }
        }
        iterateAndNextNull(nodep->thensp());
        iterateAndNextNull(nodep->elsesp());
        iterateAndNextNull(nodep->op4p());
    }
    void visit(AstLoopTest* const nodep) override {
        VL_RESTORER(m_expectFourStateExpr);
        m_expectFourStateExpr = hasAttrFourState(nodep->condp());
        iterateAndNextNull(nodep->condp());
        if (expectsFourStateExpr()) {
            wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
        }
    }
    void visit(AstWait* const nodep) override {
        {
            VL_RESTORER(m_expectFourStateExpr);
            m_expectFourStateExpr = hasAttrFourState(nodep->condp());
            iterateAndNextNull(nodep->condp());
            if (expectsFourStateExpr()) {
                wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
            }
        }
        iterateAndNextNull(nodep->stmtsp());
    }
    void visit(AstDelay* const nodep) override {
        {
            VL_RESTORER(m_expectFourStateExpr);
            m_expectFourStateExpr = hasAttrFourState(nodep->lhsp());
            iterate(nodep->lhsp());
            if (expectsFourStateExpr()) castFourToTwo(nodep->lhsp());
        }
        iterateAndNextNull(nodep->stmtsp());
    }

#define EXPRESSION_VISITOR_COMMON \
    VL_RESTORER(m_isUnderExprp); \
    VL_RESTORER(m_expectFourStateExpr); \
    m_expectFourStateExpr |= !m_isUnderExprp && hasAttrFourState(nodep); \
    m_isUnderExprp = true;

    void visit(AstNodeExpr* const nodep) override {
        EXPRESSION_VISITOR_COMMON
        iterateChildren(nodep);
    }
    void visit(AstNodeVarRef* const nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        if (nodep->access().isReadOnly() && expectsFourStateExpr()
            && !nodep->dtypep()->isFourstate())
            castTwoToFour(nodep);
    }
    void visit(AstConst* const nodep) override {
        iterateChildren(nodep);
        if (expectsFourStateExpr() && nodep->dtypep()->isFourstate() && !nodep->num().isAnyXZ()) {
            castTwoToFour(nodep);
        }
    }
    void visit(AstRedAnd* const nodep) override {
        EXPRESSION_VISITOR_COMMON
        iterateChildren(nodep);
        if (expectsFourStateExpr()) {
            nodep->v3warn(E_UNSUPPORTED, "This operator is unsupported for four-state logic");
        }
    }
    void visit(AstRedOr* const nodep) override {
        EXPRESSION_VISITOR_COMMON
        iterateChildren(nodep);
        if (expectsFourStateExpr()) {
            nodep->v3warn(E_UNSUPPORTED, "This operator is unsupported for four-state logic");
        }
    }
    void visit(AstRedXor* const nodep) override {
        EXPRESSION_VISITOR_COMMON
        iterateChildren(nodep);
        if (expectsFourStateExpr()) {
            nodep->v3warn(E_UNSUPPORTED, "This operator is unsupported for four-state logic");
        }
    }
    void visit(AstCFuncHard* const) override {
    }  // Those are here first created so, it allows to easily to not revisit same subtree
    void visit(AstVar* const nodep) override {
        iterateChildren(nodep);
        if (nodep->attrFourState()) {
            switch (nodep->varType()) {
            case VVarType::PORT:
            case VVarType::VAR:
            case VVarType::TRIOR:
            case VVarType::TRIAND:
            case VVarType::TRIWIRE:
            case VVarType::WIRE: break;
            default:
                nodep->v3warn(E_UNSUPPORTED, "Four state logic is unsupported for this type: "
                                                 << nodep->varType().ascii());
            }
        }
    }
    void visit(AstNode* const nodep) override { iterateChildren(nodep); }

public:
    explicit QuadstateVisitor(AstNetlist* nodep) {
        iterate(nodep);
        triorTriandReduce(m_assignWToTriand, VCFunc::FOUR_STATE_TRIAND_AND);
        triorTriandReduce(m_assignWToTrior, VCFunc::FOUR_STATE_TRIOR_OR);
        triorTriandReduce(m_assignWToWire, VCFunc::FOUR_STATE_TRIOR_CONFLICT);
    }
    ~QuadstateVisitor() override = default;
};

void V3Quadstate::quadstateReduce(AstNetlist* nodep) {
    if (!v3Global.opt.fourstate()) {
        UINFO(2, __FUNCTION__ << ":");
        QuadstateTypeReducerVisitor{nodep};
        V3Global::dumpCheckGlobalTree("quadstate_reduce", 0, dumpTreeEitherLevel() >= 6);
    }
}

void V3Quadstate::quadstateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    quadstateReduce(nodep);
    { QuadstateVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("quadstate", 0, dumpTreeEitherLevel() >= 6);
}
