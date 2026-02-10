#include "V3PchAstNoMT.h"

#include "V3Quadstate.h"

#include <map>
#include <set>

VL_DEFINE_DEBUG_FUNCTIONS;

class QuadstateVisitor final : public VNVisitor {
    std::map<const AstVar*, std::set<AstAssignW*>> m_assignWToTriorOrTriand;

    void visit(AstAssignW* const nodep) override {
        if (AstVarRef* const varRefp = VN_CAST(nodep->lhsp(), VarRef)) {
            if (varRefp->varp()->isWiredNet()) {
                m_assignWToTriorOrTriand[varRefp->varp()].insert(nodep);
            }
        } else {
            nodep->v3warn(EC_INFO,
                          "assign with complex lhs is unsupported in 4-state logic context");
        }
        iterateChildren(nodep);
    }
    void visit(AstNode* const nodep) override { iterateChildren(nodep); }

public:
    explicit QuadstateVisitor(AstNetlist* nodep) {
        iterate(nodep);
        for (const auto& pair : m_assignWToTriorOrTriand) {
            const std::set<AstAssignW*>& assignps = pair.second;
            if (assignps.size() < 2) continue;
            AstNodeExpr* curExprp = nullptr;
            AstAssignW* firstAssignp = nullptr;
            for (AstAssignW* const assignp : assignps) {
                AstNodeExpr* const exprp = assignp->rhsp()->unlinkFrBack();
                if (!curExprp) {
                    firstAssignp = assignp;
                    curExprp = exprp;
                } else {
                    exprp->addNext(curExprp);
                    curExprp = new AstCFuncHard{curExprp->fileline(), VCFunc::FOUR_STATE_TRIOR_OR,
                                                exprp};
                    curExprp->dtypep(exprp->dtypep());
                    pushDeletep(assignp->unlinkFrBack());
                }
            }
            firstAssignp->rhsp(curExprp);
        }
    }
    ~QuadstateVisitor() override = default;
};

void V3Quadstate::quadstateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { QuadstateVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("quadstate", 0, dumpTreeEitherLevel() >= 6);
}
