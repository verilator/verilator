// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test: transition bin with unsupported repetition operator causes empty transition set

module t;
    logic [3:0] cp_expr;

    covergroup cg;
        cp1: coverpoint cp_expr {
            bins t1 = (1 [*2]);
        }
    endgroup

    cg cg_inst = new;
    initial $finish;
endmodule
