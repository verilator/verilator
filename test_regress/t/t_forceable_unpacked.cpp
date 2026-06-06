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
    auto& en_a = topp->rootp->t__DOT__var_arr_a__VforceEn;
    auto& val_a = topp->rootp->t__DOT__var_arr_a__VforceVal;
    while (!contextp->gotFinish()) {
        topp->clk = !topp->clk;
        topp->eval();
        if (topp->clk) {
            bool changed = true;
            switch (topp->cyc) {
            case 1:
                en[0][1] = 0x3;
                val[0][1] = 0x3;
                en_a[0][1] = 0x3;
                val_a[0][1] = 0x2;
                break;
            case 2:
                en[1][0] = 0x3;
                val[1][0] = 0x2;
                en_a[1][0] = 0x3;
                val_a[1][0] = 0x3;
                break;
            case 3:
                en[0][1] = 0x0;
                en_a[0][1] = 0x0;
                break;
            case 4:
                en[1][0] = 0x0;
                en_a[1][0] = 0x0;
                break;

            default: changed = false;
            }
            if (changed) topp->eval();
        }
        contextp->timeInc(5);
    }
    return 0;
}
