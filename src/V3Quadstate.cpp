#include "V3PchAstNoMT.h"

#include "V3Quadstate.h"

#include <map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class QuadstateTypeReducerVisitor final : public VNVisitor {
    static void reduceToTwoStateLogic(AstNode* const nodep) {
        if (!nodep->dtypep() || !nodep->dtypep()->isFourstate()) return;
        if (const AstBasicDType* const dtypep = VN_CAST(nodep->dtypep(), BasicDType)) {
            switch (dtypep->keyword()) {
            case VBasicDTypeKwd::LOGIC:
            case VBasicDTypeKwd::LOGIC_IMPLICIT:
                nodep->dtypep(
                    nodep->findBitDType(dtypep->width(), dtypep->widthMin(), dtypep->numeric()));
                break;
            case VBasicDTypeKwd::INTEGER: nodep->dtypep(nodep->findIntDType()); break;
            case VBasicDTypeKwd::TIME: nodep->dtypeSetUInt64(); break;
            default:
                nodep->v3fatalSrc(
                    "Unhandled four state variable type: " << dtypep->keyword().ascii());
            }
        }
    }
    void visit(AstVar* const nodep) override {
        if (!nodep->attrFourState()) reduceToTwoStateLogic(nodep);
    }
    void visit(AstNodeExpr* const nodep) override {
        iterateChildren(nodep);
        if (!nodep->isFourState()) reduceToTwoStateLogic(nodep);
    }
    void visit(AstNodeAssign* const nodep) override {
        iterateChildren(nodep);
        nodep->dtypep(nodep->lhsp()->dtypep());
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
        if (AstVarRef* const varRefp = VN_CAST(nodep->lhsp(), VarRef)) {
            switch (varRefp->varp()->varType()) {
            case VVarType::TRIOR: m_assignWToTrior[varRefp->varp()].push_back(nodep); break;
            case VVarType::TRIAND: m_assignWToTriand[varRefp->varp()].push_back(nodep); break;
            case VVarType::TRIWIRE:
            case VVarType::WIRE: m_assignWToWire[varRefp->varp()].push_back(nodep); break;
            default: break;
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
