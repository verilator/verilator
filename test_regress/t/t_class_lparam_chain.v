// DESCRIPTION: Verilator: Verilog Test module
//
// localparams that chain through a class-scope-resolved localparam
// (typedef alias of a parameterized class, e.g. inst::b). V3LinkDot defers
// the inst::b Dot until post-V3Param; V3Param must also defer any
// localparam whose value transitively depends on a deferred one, including
// same-module VarRef chains (b -> c -> d) and not just cross-module
// VarXRefs.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  virtual class C #(parameter int a);
    localparam int b = a;
  endclass

  typedef C#(0)  inst0;
  typedef C#(42) inst42;

  // Direct: inst::b Dot in the value
  localparam int b0  = inst0::b;
  localparam int b42 = inst42::b;

  // One-step chain: refers to a deferred lparam
  localparam int c0  = b0;
  localparam int c42 = b42;

  // Multi-step chain: d -> c -> b -> inst::b
  localparam int d0  = c0;
  localparam int d42 = c42;

  // Expression referencing two deferred lparams
  localparam int sum = b0 + b42;

  initial begin
    `checkh(b0, 32'd0);
    `checkh(b42, 32'd42);
    `checkh(c0, 32'd0);
    `checkh(c42, 32'd42);
    `checkh(d0, 32'd0);
    `checkh(d42, 32'd42);
    `checkh(sum, 32'd42);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
