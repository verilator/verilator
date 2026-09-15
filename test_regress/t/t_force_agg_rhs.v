// DESCRIPTION: Verilator: Verilog Test module
//
// Asserts that a 'force' right-hand side on an aggregate leaf is re-evaluated
// when its operands change, per IEEE 1800-2023 10.6.2, just as a scalar force
// target is.
//
// Each section below states what it asserts:
//  1. an aggregate-leaf force right-hand side tracking an operand change made
//     through a function call,
//  2. a force right-hand side reading a forced sibling element of the same
//     array, which sees that sibling's force rather than raw storage.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;

  logic [7:0] fa[0:1];
  logic [7:0] fsrc;

  // A force right-hand side is re-evaluated when its operands change, including
  // through a function call, so this is used to force an element from src
  function automatic logic [7:0] xf(input logic [7:0] v);
    return {v[0], v[7:1]} ^ 8'h5a;
  endfunction

  initial begin
    //=======================================================================
    // 1. A force right-hand side on an aggregate leaf tracks a later change of
    //     its operands through a function call, as a scalar force target does.
    //=======================================================================
    fa[0] = 8'h10;
    fa[1] = 8'h20;
    fsrc = 8'h24;
    #1;
    force fa[1] = xf(fsrc);
    #1;
    `checkh(fa[1], 8'h48);
    fsrc = 8'hc3;
    #1;
    `checkh(fa[1], 8'hbb);
    release fa[1];
    #1;

    //=======================================================================
    // 2. A force right-hand side that reads a sibling element of the same
    //     array sees that sibling's own force, not raw storage.  Only a read
    //     reaching back into the force's own element stays raw, to avoid a
    //     combinational cycle.
    //=======================================================================
    fa[0] = 8'h10;
    fa[1] = 8'h20;
    #1;
    force fa[1] = fa[0] + 8'd5;
    #1;
    `checkh(fa[1], 8'h15);
    force fa[0] = 8'h40;
    #1;
    // fa[1]'s right-hand side sees the forced fa[0], not the raw value
    `checkh(fa[1], 8'h45);
    // A procedural write to the forced fa[0] does not leak through
    fa[0] = 8'h99;
    #1;
    `checkh(fa[0], 8'h40);
    `checkh(fa[1], 8'h45);
    release fa[0];
    release fa[1];
    #1;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
