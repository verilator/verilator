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
        if (!dtypep->isFourstate()) return dtypep;
        dtypep = dtypep->skipRefp();
        const auto it = m_typesToReduced.find(dtypep);
        if (it != m_typesToReduced.end()) return it->second;
        if (const AstBasicDType* const basicDtypep = VN_CAST(dtypep, BasicDType)) {
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
        } else if (AstNodeArrayDType* const arrayDtypep = VN_CAST(dtypep, NodeArrayDType)) {
            AstNodeArrayDType* const newp = arrayDtypep->cloneTree(false);
            newp->refDTypep(reduceTypeToTwoStateLogic(arrayDtypep->subDTypep()));
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_typesToReduced.insert({dtypep, newp});
            return newp;
        } else if (AstSampleQueueDType* const queueDtypep = VN_CAST(dtypep, SampleQueueDType)) {
            AstSampleQueueDType* const newp = queueDtypep->cloneTree(false);
            newp->refDTypep(reduceTypeToTwoStateLogic(queueDtypep->subDTypep()));
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_typesToReduced.insert({dtypep, newp});
            return newp;
        } else if (AstNodeUOrStructDType* const structDtypep
                   = VN_CAST(dtypep, NodeUOrStructDType)) {
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

    void visit(AstAssignW* const nodep) override {
        if (const AstVarRef* const varRefp = VN_CAST(nodep->lhsp(), VarRef)) {
            const AstVar* const varp = varRefp->varp();
            if (varp->attrFourState()) {
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
    UINFO(2, __FUNCTION__ << ":");
    { QuadstateTypeReducerVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("quadstate_reduce", 0, dumpTreeEitherLevel() >= 6);
}

void V3Quadstate::quadstateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    quadstateReduce(nodep);
    { QuadstateVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("quadstate", 0, dumpTreeEitherLevel() >= 6);
}
