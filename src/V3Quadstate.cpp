#include "V3PchAstNoMT.h"

#include "V3Quadstate.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class QuadstateVisitor final : public VNVisitor {
    void visit(AstNode* const nodep) override { iterateChildren(nodep); }

public:
    explicit QuadstateVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~QuadstateVisitor() override = default;
};

void V3Quadstate::quadstateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { QuadstateVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("quadstate", 0, dumpTreeEitherLevel() >= 6);
}
