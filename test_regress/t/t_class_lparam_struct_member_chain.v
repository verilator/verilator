// DESCRIPTION: Verilator: Verilog Test module
//
// A struct typedef whose member references a class-scope-resolved typedef
// from a parameterized-class typedef alias (e.g. CFG::data_t). The struct
// is consumed by `$bits(...)` on a cell parameter pin, which forces V3Param
// to constify the pin during cell deparameterization. V3Param must follow
// typedef references in the pin tree and resolve the unresolved struct-member
// RefDTypes that target the parameterized class, otherwise V3Width hits
// "REFDTYPE 'data_t' not linked to type" (V3AstNodes.cpp).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

package pkg;
  virtual class C #(parameter int W = 1);
    typedef logic [W-1:0] data_t;
  endclass
endpackage

module Sink #(parameter int BITS = 1) ();
  logic [BITS-1:0] data;
endmodule

module Sub #(parameter int W = 8) ();
  typedef pkg::C#(W) CFG;

  // Struct typedef whose member is a class-scope-resolved typedef from
  // a parameterized-class typedef alias. Without the V3Param fix, the
  // member's RefDType stays UNLINKED and the cell pin's $bits trips an
  // internal error.
  typedef struct packed {
    CFG::data_t payload;
    logic       v;
  } wrap_t;

  Sink #(.BITS($bits(wrap_t))) u_sink ();
endmodule

module t;
  Sub #(.W(8)) u ();

  initial begin
    // $bits(wrap_t) = 8 (payload) + 1 (v) = 9
    `checkh($bits(u.u_sink.data), 32'd9);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
