#include "V3PchAstNoMT.h"

#include "V3Quadstate.h"

#include <map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class QuadstateTypeReducerVisitor final : public VNVisitor {
    static AstNodeDType* reduceTypeToTwoStateLogic(AstNodeDType* dtypep) {
        if (!dtypep) return nullptr;
        // FIXME: this is terrible since we call this for each Expr and this function in almost
        // each extp travels a whole subtree
        if (const AstRefDType* const refDtypep = VN_CAST(dtypep, RefDType)) {
            if (!refDtypep->typedefp() && !refDtypep->subDTypep()) return dtypep;
        }
        {
            AstNodeDType* const newp = dtypep->skipRefp();
            if (dtypep != newp) {
                dtypep->deleteTree();
                dtypep = newp->cloneTree(false);
            } else {
                dtypep = newp;
            }
        }
        if (const AstBasicDType* const basicDtypep = VN_CAST(dtypep, BasicDType)) {
            if (!basicDtypep->isFourstate()) return dtypep;
            VBasicDTypeKwd basicDTypeKwd;
            switch (basicDtypep->keyword()) {
            case VBasicDTypeKwd::LOGIC_IMPLICIT:
                basicDTypeKwd = VBasicDTypeKwd::BIT_IMPLICIT;
                break;
            case VBasicDTypeKwd::LOGIC: basicDTypeKwd = VBasicDTypeKwd::BIT; break;
            case VBasicDTypeKwd::INTEGER: basicDTypeKwd = VBasicDTypeKwd::UINT32; break;
            case VBasicDTypeKwd::TIME: basicDTypeKwd = VBasicDTypeKwd::UINT64; break;
            default:
                basicDtypep->v3fatalSrc(
                    "Unhandled four state variable type: " << basicDtypep->keyword().ascii());
            }
            AstBasicDType* const newp
                = new AstBasicDType{dtypep->fileline(), basicDTypeKwd, basicDtypep->numeric(),
                                    basicDtypep->width(), basicDtypep->widthMin()};
            if (basicDtypep->rangep()) newp->rangep(basicDtypep->rangep()->unlinkFrBack());
            dtypep->deleteTree();
            return newp;
        }
        if (AstNodeArrayDType* const arrayDtypep = VN_CAST(dtypep, NodeArrayDType)) {
            // AstNodeArrayDType* const newp = arrayDtypep->cloneTree(false);
            arrayDtypep->childDTypep(
                reduceTypeToTwoStateLogic(arrayDtypep->childDTypep()->unlinkFrBack()));
            // v3Global.rootp()->typeTablep()->addTypesp(newp);
            return arrayDtypep;
        }
        if (AstDynArrayDType* const arrayDtypep = VN_CAST(dtypep, DynArrayDType)) {
            // AstDynArrayDType* const newp = arrayDtypep->cloneTree(false);
            arrayDtypep->childDTypep(
                reduceTypeToTwoStateLogic(arrayDtypep->childDTypep()->unlinkFrBack()));
            // v3Global.rootp()->typeTablep()->addTypesp(newp);
            return arrayDtypep;
        }
        if (AstWildcardArrayDType* const arrayDtypep = VN_CAST(dtypep, WildcardArrayDType)) {
            // AstWildcardArrayDType* const newp = arrayDtypep->cloneTree(false);
            arrayDtypep->childDTypep(
                reduceTypeToTwoStateLogic(arrayDtypep->childDTypep()->unlinkFrBack()));
            // v3Global.rootp()->typeTablep()->addTypesp(newp);
            return arrayDtypep;
        }
        if (AstSampleQueueDType* const queueDtypep = VN_CAST(dtypep, SampleQueueDType)) {
            // AstSampleQueueDType* const newp = queueDtypep->cloneTree(false);
            queueDtypep->childDTypep(
                reduceTypeToTwoStateLogic(queueDtypep->childDTypep()->unlinkFrBack()));
            // v3Global.rootp()->typeTablep()->addTypesp(newp);
            return queueDtypep;
        }
        if (AstQueueDType* const queueDtypep = VN_CAST(dtypep, QueueDType)) {
            // AstQueueDType* const newp = queueDtypep->cloneTree(false);
            queueDtypep->childDTypep(
                reduceTypeToTwoStateLogic(queueDtypep->childDTypep()->unlinkFrBack()));
            // v3Global.rootp()->typeTablep()->addTypesp(newp);
            return queueDtypep;
        }
        if (AstBracketArrayDType* const bracketArrayDtypep = VN_CAST(dtypep, BracketArrayDType)) {
            // AstQueueDType* const newp = bracketArrayDtypep->cloneTree(false);
            bracketArrayDtypep->childDTypep(
                reduceTypeToTwoStateLogic(bracketArrayDtypep->childDTypep()->unlinkFrBack()));
            // v3Global.rootp()->typeTablep()->addTypesp(newp);
            return bracketArrayDtypep;
        }
        if (AstNodeUOrStructDType* const structDtypep = VN_CAST(dtypep, NodeUOrStructDType)) {
            // AstNodeUOrStructDType* const newp = structDtypep->cloneTree(false);
            for (AstMemberDType* memberp = structDtypep->membersp(); memberp;
                 memberp = VN_AS(memberp->nextp(), MemberDType)) {
                AstNodeDType* const newMemberDTypep
                    = reduceTypeToTwoStateLogic(memberp->childDTypep()->unlinkFrBack());
                memberp->childDTypep(newMemberDTypep);
                // memberp->dtypep(newMemberDTypep);
            }
            structDtypep->isFourstate(false);  // FIXME: allow four_state pragma in structs
            // v3Global.rootp()->typeTablep()->addTypesp(newp);
            return structDtypep;
        }
        if (AstAssocArrayDType* const arrayDtypep = VN_CAST(dtypep, AssocArrayDType)) {
            // AstAssocArrayDType* const newp = arrayDtypep->cloneTree(false);
            arrayDtypep->refDTypep(
                reduceTypeToTwoStateLogic(arrayDtypep->subDTypep()->unlinkFrBack()));
            arrayDtypep->keyDTypep(
                reduceTypeToTwoStateLogic(arrayDtypep->keyDTypep()->unlinkFrBack()));
            // v3Global.rootp()->typeTablep()->addTypesp(newp);
            return arrayDtypep;
        }
        if (VN_IS(dtypep, VoidDType) || VN_IS(dtypep, ClassRefDType)
            || VN_IS(dtypep, IfaceRefDType) || VN_IS(dtypep, NBACommitQueueDType)
            || VN_IS(dtypep, CDType)) {
            return dtypep;
        }
        dtypep->v3fatalSrc("Unhandled DType: " << dtypep);
    }

    void visit(AstVar* const nodep) override {
        iterateChildren(nodep);
        if (!nodep->attrFourState() && nodep->getChildDTypep()) {
            nodep->childDTypep(reduceTypeToTwoStateLogic(nodep->getChildDTypep()->unlinkFrBack()));
        }
    }
    // void visit(AstNodeExpr* const nodep) override {
    //     iterateChildren(nodep);
    //     if (!nodep->isFourState())
    //         nodep->dtypep(reduceTypeToTwoStateLogic(nodep->getChildDTypep()));
    // }
    // void visit(AstNodeAssign* const nodep) override {
    //     iterateChildren(nodep);
    //     nodep->dtypep(nodep->lhsp()->dtypep());
    // }
    // void visit(AstConsPackUOrStruct* const nodep) override {
    //     if (!nodep->isFourState()) {
    //         nodep->dtypep(reduceTypeToTwoStateLogic(nodep->dtypep()));
    //         AstMemberDType* dtypep = VN_AS(nodep->dtypep(), NodeUOrStructDType)->membersp();
    //         for (AstConsPackMember* memberp = nodep->membersp(); memberp;
    //              memberp = VN_AS(memberp->nextp(), ConsPackMember)) {
    //             memberp->dtypep(dtypep);
    //             dtypep = VN_AS(dtypep->nextp(), MemberDType);
    //             iterateChildren(memberp);
    //         }
    //     }
    // }
    // void visit(AstConsPackMember* const nodep) override {
    //     nodep->v3fatalSrc("This node shall never be visited here");
    // }
    void visit(AstNode* const nodep) override { iterateChildren(nodep); }

public:
    explicit QuadstateTypeReducerVisitor(AstNode* nodep) { iterate(nodep); }
    ~QuadstateTypeReducerVisitor() override = default;
};

class QuadstateVisitor final : public VNVisitor {
    std::map<const AstVar*, std::vector<AstAssignW*>> m_assignWToTrior;
    std::map<const AstVar*, std::vector<AstAssignW*>> m_assignWToTriand;
    std::map<const AstVar*, std::vector<AstAssignW*>> m_assignWToWire;

    static AstNodeExpr* buildTree(std::vector<AstNodeExpr*> exprps, const VCFunc reductor) {
        while (exprps.size() > 1) {
            const size_t halfSize = exprps.size() / 2;
            for (size_t i = 0; i < halfSize; ++i) {
                AstNodeDType* const dtypep = exprps[i]->dtypep();
                exprps[i] = new AstCFuncHard{exprps[i]->fileline(), reductor,
                                             exprps[i]->addNext(exprps.back())};
                exprps[i]->dtypeSetLogicUnsized(dtypep->width(), dtypep->widthMin(),
                                                dtypep->numeric());
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
        return exprp->exists([](const AstVarRef* const varRefp) {
            return v3Global.opt.fourstate() || varRefp->varp()->attrFourState();
        }) || (v3Global.opt.fourstateLiterals() && exprp->exists([](const AstConst* const nodep) {
                   return nodep->isFourState();
               }));
    }

    static AstCFuncHard* wrapExprpInCFuncHard(AstNodeExpr* const exprp, const VCFunc func) {
        VNRelinker relinker;
        exprp->unlinkFrBack(&relinker);
        AstCFuncHard* const newp = new AstCFuncHard{exprp->fileline(), func, exprp};
        relinker.relink(newp);
        return newp;
    }

    void visit(AstAssignW* const nodep) override {
        if (const AstVarRef* const varRefp = VN_CAST(nodep->lhsp(), VarRef)) {
            const AstVar* const varp = varRefp->varp();
            if (v3Global.opt.fourstate() || varp->attrFourState()) {
                switch (varp->varType()) {
                case VVarType::TRIOR: m_assignWToTrior[varp].push_back(nodep); break;
                case VVarType::TRIAND: m_assignWToTriand[varp].push_back(nodep); break;
                case VVarType::TRIWIRE:
                case VVarType::WIRE: m_assignWToWire[varp].push_back(nodep); break;
                default: break;
                }
            }
        } else if (nodep->lhsp()->isFourState()) {
            nodep->v3warn(EC_INFO,
                          "assign with complex lhs is unsupported in 4-state logic context");
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeIf* const nodep) override {
        if (hasAttrFourState(nodep->condp())) {
            wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
        }
        iterateChildren(nodep);
    }
    void visit(AstCond* const nodep) override {
        if (hasAttrFourState(nodep->condp())) {
            wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
        }
        iterateChildren(nodep);
    }
    void visit(AstLoopTest* const nodep) override {
        iterateAndNextNull(nodep->condp());
        if (hasAttrFourState(nodep->condp())) {
            wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
        }
    }
    void visit(AstWait* const nodep) override {
        if (hasAttrFourState(nodep->condp())) {
            wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
        }
        iterateChildren(nodep);
    }
    void visit(AstDelay* const nodep) override {
        if (AstConst* const constp = VN_CAST(nodep->lhsp(), Const)) {
            if (!constp->num().isAnyXZ()) constp->dtypeSetUInt64();
        }
        if (hasAttrFourState(nodep->lhsp())) {
            const AstNodeDType* const dtypep = nodep->lhsp()->dtypep();
            wrapExprpInCFuncHard(nodep->lhsp(), VCFunc::FOUR_STATE_TWO_STATE_VALUE)
                ->dtypeSetBitSized(dtypep->width(), dtypep->numeric());
        }
        iterateChildren(nodep);
    }

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

void V3Quadstate::quadstateReduce(AstNode* nodep) {
    // if (!v3Global.opt.fourstate()) {
    //     UINFO(2, __FUNCTION__ << ":");
    //     QuadstateTypeReducerVisitor{nodep};
    // }
}

void V3Quadstate::quadstateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { QuadstateVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("quadstate", 0, dumpTreeEitherLevel() >= 6);
}
