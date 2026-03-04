#include "V3PchAstNoMT.h"

#include "V3Quadstate.h"

#include <map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

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

    void visit(AstAssignW* const nodep) override {
        if (const AstVarRef* const varRefp = VN_CAST(nodep->lhsp(), VarRef)) {
            const AstVar* const varp = varRefp->varp();
            if (v3Global.opt.fourstate() && varRefp->dtypep()->isFourstate()) {
                switch (varp->varType()) {
                case VVarType::TRIOR: m_assignWToTrior[varp].push_back(nodep); break;
                case VVarType::TRIAND: m_assignWToTriand[varp].push_back(nodep); break;
                case VVarType::TRIWIRE:
                case VVarType::WIRE: m_assignWToWire[varp].push_back(nodep); break;
                default: break;
                }
            }
        } else if (nodep->lhsp()->dtypep()->isFourstate()) {
            nodep->v3warn(EC_INFO,
                          "assign with complex lhs is unsupported in 4-state logic context");
        }
        iterateChildren(nodep);
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

void V3Quadstate::quadstateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { QuadstateVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("quadstate", 0, dumpTreeEitherLevel() >= 6);
}
