// -*- mode: C++; c-file-style: "cc-mode" -*-

#ifndef _V3DYNAMIC_H_
#define _V3DYNAMIC_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

class V3Dynamic {
public:
    // CONSTRUCTORS
    static void markDynamic(AstNetlist* nodep);
};

#endif  // Guard
