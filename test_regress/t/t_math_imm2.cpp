// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include "Vt_math_imm2.h"

QData MaskVal(int lbit, int hbit) {
    QData val;
    for (val = 0; lbit <= hbit; lbit++)
        val |= (1ULL << lbit);
    return val;
}

int main(int argc, char* argv[]) {
    Verilated::debug(0);

    Vt_math_imm2* sim = new Vt_math_imm2;
    int lbit, hbit;

    int errs = 0;
    for (lbit = 0; lbit < 32; lbit++) {
        for (hbit = lbit; hbit < 32; hbit++) {
            QData expected;

            sim->LowMaskSel_Bot = lbit;
            sim->LowMaskSel_Top = lbit;
            sim->HighMaskSel_Bot = hbit;
            sim->HighMaskSel_Top = hbit;

            sim->eval();

            expected = ((MaskVal(sim->LowMaskSel_Top, sim->HighMaskSel_Top) << 32ULL)
                        | MaskVal(sim->LowMaskSel_Bot, sim->HighMaskSel_Bot));

            if (sim->LogicImm != expected) {
                printf("%%Error: %d.%d,%d.%d -> %016" VL_PRI64 "x/%016" VL_PRI64 "x -> %016" VL_PRI64 "x (expected %016" VL_PRI64 "x)\n",
                       sim->LowMaskSel_Top, sim->HighMaskSel_Top,
                       sim->LowMaskSel_Bot, sim->HighMaskSel_Bot,
                       sim->LowLogicImm, sim->HighLogicImm,
                       sim->LogicImm,  expected);
                errs=1;
            }
        }
    }

    if (errs) {
        vl_stop(__FILE__, __LINE__, "TOP-cpp");
        exit(10);
    } else {
        printf("*-* All Finished *-*\n");
        exit(0);
    }
}
