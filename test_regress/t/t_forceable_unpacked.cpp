// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

#include "verilatedos.h"

#include "verilated.h"

#include <memory>
#include VM_PREFIX_INCLUDE
#include VM_PREFIX_ROOT_INCLUDE

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{"top"}};
    auto& en = topp->rootp->t__DOT__var_arr__VforceEn;
    auto& val = topp->rootp->t__DOT__var_arr__VforceVal;
    while (!contextp->gotFinish()) {
        topp->clk = !topp->clk;
        topp->eval();
        if (topp->clk) {
            bool changed = true;
            switch (topp->cyc) {
            case 4:
                en[0][1] = 0xf;
                val[0][1] = 0xa;
                break;
            case 5:
                en[1][0] = 0xf;
                val[1][0] = 0xb;
                break;
            case 7: en[0][1] = 0; break;
            case 9: en[1][0] = 0; break;
            default: changed = false;
            }
            if (changed) topp->eval();
        }
        contextp->timeInc(5);
    }
    return 0;
}
