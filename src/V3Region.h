// -*- mode: C++; c-file-style: "cc-mode" -*-

#ifndef _V3REGION_H_
#define _V3REGION_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

class V3Region {
public:
    // CONSTRUCTORS
    static void assignRegions(AstNetlist* nodep);
};

#endif  // Guard
