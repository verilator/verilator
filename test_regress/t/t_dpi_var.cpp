// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include VM_PREFIX_INCLUDE
#include "verilated.h"
#include "svdpi.h"

#include "verilated_syms.h"

//======================================================================

struct MyMon {
    vluint32_t* sigsp[2];
    MyMon() {
        sigsp[0] = NULL;
        sigsp[1] = NULL;
    }
};
MyMon mons[2];

void mon_register_a(const char* namep, void* sigp, bool isOut) {
    // Callback from initial block in monitor
#ifdef TEST_VERBOSE
    VL_PRINTF("-     mon_register_a(\"%s\", %p, %d);\n", namep, sigp, isOut);
#endif
    mons[0].sigsp[isOut] = (vluint32_t*)sigp;
}

void mon_do(MyMon* monp) {
    if (!monp->sigsp[0]) vl_fatal(__FILE__, __LINE__, "", "never registered");
    if (!monp->sigsp[1]) vl_fatal(__FILE__, __LINE__, "", "never registered");
    *monp->sigsp[1] = (*(monp->sigsp[0])) + 1;

#ifdef TEST_VERBOSE
    VL_PRINTF("-     mon_do(%08x(&%p) -> %08x(&%p));\n", *(monp->sigsp[0]), monp->sigsp[0],
              *(monp->sigsp[1]), monp->sigsp[1]);
#endif
}

void mon_class_name(const char* namep) {
#ifdef TEST_VERBOSE
    VL_PRINTF("-     mon_class_name(\"%s\");\n", namep);
#endif
    // Check the C's calling name of "" doesn't lead to extra dots in the name()
    if (namep && namep[0] == '.')
        vl_fatal(__FILE__, __LINE__, "", (std::string("Unexp class name ") + namep).c_str());
}

extern "C" void mon_scope_name(const char* namep);
void mon_scope_name(const char* namep) {
    const char* modp = svGetNameFromScope(svGetScope());
#ifdef TEST_VERBOSE
    VL_PRINTF("-     mon_scope_name('%s', \"%s\");\n", modp, namep);
#endif
    if (strcmp(namep, "t.sub"))
        vl_fatal(__FILE__, __LINE__, "", (std::string("Unexp scope name ") + namep).c_str());
    if (strcmp(modp, "t.sub"))
        vl_fatal(__FILE__, __LINE__, "", (std::string("Unexp dpiscope name ") + modp).c_str());
}

extern "C" void mon_register_b(const char* namep, int isOut);
void mon_register_b(const char* namep, int isOut) {
    const char* modp = svGetNameFromScope(svGetScope());
#ifdef TEST_VERBOSE
    VL_PRINTF("-     mon_register_b('%s', \"%s\", %d);\n", modp, namep, isOut);
#endif
    // Use scope to get pointer and size of signal
    const VerilatedScope* scopep = Verilated::dpiScope();
    const VerilatedVar* varp = scopep->varFind(namep);
    if (!varp) {
        VL_PRINTF("%%Warning: mon_register_b signal not found: \"%s\"\n", namep);
    } else if (varp->vltype() != VLVT_UINT32) {
        VL_PRINTF("%%Warning: wrong type for signal: \"%s\"\n", namep);
    } else {
        vluint32_t* datap = (vluint32_t*)(varp->datap());
        VL_PRINTF("-     mon_register_b('%s', \"%s\", %p, %d);\n", modp, namep, datap, isOut);
        mons[1].sigsp[isOut] = (vluint32_t*)(varp->datap());
    }
}

extern "C" void mon_register_done();
void mon_register_done() {
#ifdef TEST_VERBOSE
    const char* modp = svGetNameFromScope(svGetScope());
    VL_PRINTF("-     mon_register_done('%s');\n", modp);
#endif
    // Print list of all signals - if we didn't register2 anything we'd pick them off here
    const VerilatedScope* scopep = Verilated::dpiScope();
    if (VerilatedVarNameMap* varsp = scopep->varsp()) {
        for (VerilatedVarNameMap::const_iterator it = varsp->begin(); it != varsp->end(); ++it) {
            VL_PRINTF("-       mon2: %s\n", it->first);
        }
    }
}

extern "C" void mon_eval();
void mon_eval() {
    // Callback from always@ negedge
    mon_do(&mons[0]);
    mon_do(&mons[1]);
}

//======================================================================

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }
int main(int argc, char** argv, char** env) {
    double sim_time = 1100;
    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);

    VM_PREFIX* topp = new VM_PREFIX("");  // Note null name - we're flattening it out

#ifdef VERILATOR
# ifdef TEST_VERBOSE
    Verilated::scopesDump();
# endif
#endif

    topp->eval();
    topp->clk = 0;
    main_time += 10;

    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {
        main_time += 1;
        topp->eval();
        topp->clk = !topp->clk;
        // mon_do();
    }
    if (!Verilated::gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    VL_DO_DANGLING(delete topp, topp);
    exit(0L);
}
