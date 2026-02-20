// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Tests for automatic bins error conditions

module t;
    int size_var;
    logic [3:0] cp_expr;

    // Error: array size must be a constant
    covergroup cg1;
        cp1: coverpoint cp_expr {
            bins auto[size_var];
        }
    endgroup

    // Error: array size must be 1-10000 (zero)
    covergroup cg2;
        cp1: coverpoint cp_expr {
            bins auto[0];
        }
    endgroup

    // Error: array size must be 1-10000 (too large)
    covergroup cg3;
        cp1: coverpoint cp_expr {
            bins auto[10001];
        }
    endgroup

    cg1 cg1_inst = new;
    cg2 cg2_inst = new;
    cg3 cg3_inst = new;

    initial $finish;
endmodule
