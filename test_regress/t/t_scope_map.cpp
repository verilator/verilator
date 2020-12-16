// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_syms.h>
#include <verilated_vcd_c.h>
#include <map>
#include <string>

#include "Vt_scope_map.h"

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

const unsigned long long dt_2 = 3;

int main(int argc, char** argv, char** env) {
    Vt_scope_map* top = new Vt_scope_map("top");

    Verilated::debug(0);
    Verilated::traceEverOn(true);

    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");

    top->CLK = 0;
    top->eval();
    tfp->dump((unsigned int)(main_time));
    ++main_time;

    const VerilatedScopeNameMap* scopeMapp = Verilated::scopeNameMap();
    for (VerilatedScopeNameMap::const_iterator it = scopeMapp->begin(); it != scopeMapp->end();
         ++it) {
#ifdef TEST_VERBOSE
        VL_PRINTF("---------------------------------------------\n");
        VL_PRINTF("Scope = %s\n", it->first);
        it->second->scopeDump();
#endif
        VerilatedVarNameMap* varNameMap = it->second->varsp();
        if (!varNameMap) {
            VL_PRINTF("%%Error: Bad varsp()\n");
            return -1;
        }

        for (const auto& varname : *varNameMap) {
            const VerilatedVar* varp = &(varname.second);
            int varLeft = varp->packed().left();
            int varRight = varp->packed().right();

#ifdef TEST_VERBOSE
            VL_PRINTF("\tVar = %s\n", varname.first);
            VL_PRINTF("\t  Type = %d\n", varp->vltype());
            VL_PRINTF("\t  EntSize = %d\n", varp->entSize());
            VL_PRINTF("\t  Dims = %d\n", varp->dims());
            VL_PRINTF("\t  Range = %d:%d\n", varLeft, varRight);
            VL_PRINTF("\t  Is RW = %d\n", varp->isPublicRW());
#endif

            if (varRight != 0) {
                VL_PRINTF("%%Error: Was expecting right range value = 0\n");
                return -1;
            }

            int varBits = varLeft + 1;

            // First expect an incrementing byte pattern
            vluint8_t* varData = reinterpret_cast<vluint8_t*>(varp->datap());
            for (int i = 0; i < varBits / 8; i++) {
#ifdef TEST_VERBOSE
                VL_PRINTF("%02x ", varData[i]);
#endif

                vluint8_t expected = i % 0xff;
                if (varData[i] != expected) {
                    VL_PRINTF("%%Error: Data mismatch, got 0x%02x, expected 0x%02x\n", varData[i],
                              expected);
                    return -1;
                }
            }

            // Extra bits all set high initially
            if (varBits % 8 != 0) {
                vluint8_t got = varData[varBits / 8];
                vluint8_t expected = ~(0xff << (varBits % 8));
                if (got != expected) {
                    VL_PRINTF("%%Error: Data mismatch, got 0x%02x, expected 0x%02x\n", got,
                              expected);
                    return -1;
                }
            }

#ifdef TEST_VERBOSE
            VL_PRINTF("\n");
#endif

            // Clear out the data
            memset(varData, 0, (varBits + 7) / 8);
        }
    }

    top->CLK = 0;
    top->eval();
    tfp->dump((unsigned int)(main_time));
    ++main_time;

    // Posedge on clock, expect all the public bits to flip
    top->CLK = 1;
    top->eval();
    tfp->dump((unsigned int)(main_time));
    ++main_time;

    // Code coverage of historical flush function
    Verilated::flushCall();

    for (VerilatedScopeNameMap::const_iterator it = scopeMapp->begin(); it != scopeMapp->end();
         ++it) {
        VerilatedVarNameMap* varNameMap = it->second->varsp();
        if (!varNameMap) {
            VL_PRINTF("%%Error: Bad varsp()\n");
            return -1;
        }

        for (const auto& varname : *varNameMap) {
            const VerilatedVar* varp = &(varname.second);
            int varLeft = varp->packed().left();
            int varBits = varLeft + 1;
            vluint8_t* varData = reinterpret_cast<vluint8_t*>(varp->datap());

            // Check that all bits are high now
            for (int i = 0; i < varBits / 8; i++) {
                vluint8_t expected = 0xff;
                if (varData[i] != expected) {
                    VL_PRINTF("%%Error: Data mismatch (%s), got 0x%02x, expected 0x%02x\n",
                              varname.first, varData[i], expected);
                    return -1;
                }
            }

            if (varBits % 8 != 0) {
                vluint8_t got = varData[varBits / 8];
                vluint8_t expected = ~(0xff << (varBits % 8));
                if (got != expected) {
                    VL_PRINTF("%%Error: Data mismatch (%s), got 0x%02x, expected 0x%02x\n",
                              varname.first, got, expected);
                    return -1;
                }
            }
        }
    }

    top->CLK = 0;
    top->eval();
    tfp->dump((unsigned int)(main_time));
    ++main_time;

    tfp->close();
    top->final();
    VL_DO_DANGLING(delete tfp, tfp);
    VL_DO_DANGLING(delete top, top);

    VL_PRINTF("*-* All Finished *-*\n");

    return 0;
}
