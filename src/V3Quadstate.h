#ifndef VERILATOR_V3QUADSTATE_METHOD_H_
#define VERILATOR_V3QUADSTATE_METHOD_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3Quadstate final {
public:
    static void quadstateReduce(AstNode* nodep) VL_MT_DISABLED;
    static void quadstateAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
