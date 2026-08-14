// DESCRIPTION: Verilator: Verilog Test module
//
// `$bits()` of a signal whose type comes from a parameterized class
// (`CFG::data_t`, via a typedef alias of `cls#(P)`).
//
// V3LinkDot defers linking a RefDType whose scope is a parameterized class -
// it can only resolve once the class is specialized in V3Param.  V3Param
// resolves such RefDTypes where it knows to look (cell pin types, typedefs
// reachable from a pin), but a plain module-level signal is not one of those
// places; its RefDType stays unlinked until V3Width runs normally.
//
// `$bits(sig)` breaks that: constifyParamsEdit -> widthParamsEdit runs
// V3Width early, during V3Param, to fold the parameter expression.  Widthing
// the VarRef forces the Var to be widthed, which calls skipRefp() on the
// still-unlinked RefDType, giving "REFDTYPE 'data_t' not linked to type".
// Using the signal ordinarily (assignment) does not trigger it, because
// nothing forces the early width pass.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

package pkg;
  typedef struct packed {
    int depth;
  } config_t;

  virtual class cfg #(
      parameter config_t c
  );
    localparam int width = $clog2(c.depth);
    typedef logic [width-1:0] data_t;
  endclass
endpackage

// Child with a type parameter defaulted from another parameter, as in a
// sample-and-hold style utility module
module Holder #(
    parameter int  width  = 0,
    parameter type data_t = logic [width-1:0]
) (
    input  data_t dat_i,
    output data_t dat_o
);
  always_comb dat_o = dat_i;
endmodule

module Sub #(
    parameter pkg::config_t cfg
) ();
  typedef pkg::cfg #(cfg) CFG;
  CFG::data_t src, dst;

  // (1) $bits() of a class-scoped-typed signal, in a localparam
  localparam int Bits = $bits(src);

  // (2) $bits() of a class-scoped-typed signal, as a cell parameter pin
  Holder #(.width($bits(src))) holder (
      .dat_i (src),
      .dat_o (dst)
  );

  // (3) Same, inside a generate arm
  if (CFG::width > 0) begin : gen_arm
    CFG::data_t arm_src, arm_dst;
    Holder #(.width($bits(arm_src))) armHolder (
        .dat_i (arm_src),
        .dat_o (arm_dst)
    );
    initial arm_src = '0;
  end

  initial begin
    src = '0;
    `checkh(Bits, 32'd9);
    `checkh($bits(src), 32'd9);
    `checkh($bits(dst), 32'd9);
  end
endmodule

module t;
  localparam pkg::config_t CFGV = '{depth: 512};
  Sub #(.cfg(CFGV)) sub ();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
