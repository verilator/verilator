// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test: unsupported coverage option name in a coverpoint

module t;
    logic [3:0] cp_expr;

    covergroup cg;
        cp1: coverpoint cp_expr {
            option.foobar = 1;
        }
    endgroup

    cg cg_inst = new;
    initial $finish;
endmodule
