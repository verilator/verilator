#ifndef VERILATOR_V3FOURSTATE_METHOD_H_
#define VERILATOR_V3FOURSTATE_METHOD_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3Fourstate final {
public:
    static void fourstateAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
