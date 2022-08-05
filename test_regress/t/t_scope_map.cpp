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

#include "Vt_scope_map.h"

#include <map>
#include <string>

const unsigned long long dt_2 = 3;

int main(int argc, char** argv, char** env) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    Vt_scope_map* top = new Vt_scope_map{contextp.get(), "top"};

    contextp->debug(0);
    contextp->traceEverOn(true);

    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");

    top->CLK = 0;
    top->eval();
    tfp->dump(contextp->time());
    contextp->timeInc(1);

    const VerilatedScopeNameMap* scopeMapp = contextp->scopeNameMap();
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
            uint8_t* varData = reinterpret_cast<uint8_t*>(varp->datap());
            for (int i = 0; i < varBits / 8; i++) {
#ifdef TEST_VERBOSE
                VL_PRINTF("%02x ", varData[i]);
#endif

                const uint8_t expected = i % 0xff;
                if (varData[i] != expected) {
                    VL_PRINTF("%%Error: Data mismatch, got 0x%02x, expected 0x%02x\n", varData[i],
                              expected);
                    return -1;
                }
            }

            // Extra bits all set high initially
            if (varBits % 8 != 0) {
                const uint8_t got = varData[varBits / 8];
                const uint8_t expected = ~(0xff << (varBits % 8));
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
    tfp->dump(contextp->time());
    contextp->timeInc(1);

    // Posedge on clock, expect all the public bits to flip
    top->CLK = 1;
    top->eval();
    tfp->dump(contextp->time());
    contextp->timeInc(1);

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
            uint8_t* varData = reinterpret_cast<uint8_t*>(varp->datap());

            // Check that all bits are high now
            for (int i = 0; i < varBits / 8; i++) {
                const uint8_t expected = 0xff;
                if (varData[i] != expected) {
                    VL_PRINTF("%%Error: Data mismatch (%s), got 0x%02x, expected 0x%02x\n",
                              varname.first, varData[i], expected);
                    return -1;
                }
            }

            if (varBits % 8 != 0) {
                const uint8_t got = varData[varBits / 8];
                const uint8_t expected = ~(0xff << (varBits % 8));
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
    tfp->dump(contextp->time());
    contextp->timeInc(1);

    tfp->close();
    top->final();
    VL_DO_DANGLING(delete tfp, tfp);
    VL_DO_DANGLING(delete top, top);

    VL_PRINTF("*-* All Finished *-*\n");

    return 0;
}
