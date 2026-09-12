// DESCRIPTION: Verilator: Unpacked struct values as class parameters
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

package P;
  typedef struct {
    int depth;
  } memory_config_t;

  typedef struct {
    memory_config_t memory;
    int counters;
  } config_t;

  virtual class cfg #(
      parameter config_t C
  );
    localparam int WIDTH = $clog2(C.memory.depth);
    localparam int COUNTERS = C.counters;
    typedef logic [WIDTH-1:0] data_t;
  endclass

  localparam config_t PKG_CFG = '{memory: '{depth: 8192}, counters: 6};
  typedef cfg#(PKG_CFG) PkgCfg;
endpackage

package Q;
  localparam P::config_t CFG = '{memory: '{depth: 1024}, counters: 3};
  typedef P::cfg#(CFG) CrossPkgCfg;
endpackage

module Sub #(
    parameter P::config_t C
) (
    input P::cfg#(C)::data_t din
);
  initial begin
    `checkh($bits(din), $clog2(C.memory.depth));
    `checkh(C.counters, P::cfg#(C)::COUNTERS);
  end
endmodule

module t;
  localparam P::config_t CFG_A = '{memory: '{depth: 4096}, counters: 4};
  localparam P::config_t CFG_B = '{memory: '{depth: 32768}, counters: 7};
  // Equal to CFG_A, so must select the same Sub specialization.
  localparam P::config_t CFG_A2 = '{memory: '{depth: 4096}, counters: 4};
  // Differs from CFG_A only in a nested field, so must not share with it.
  localparam P::config_t CFG_C = '{memory: '{depth: 4096}, counters: 5};

  P::cfg#(CFG_A)::data_t a;
  P::cfg#(CFG_B)::data_t b;
  P::PkgCfg::data_t pkg;
  Q::CrossPkgCfg::data_t cross_pkg;

  P::cfg#(CFG_A2)::data_t a2;
  P::cfg#(CFG_C)::data_t c;

  Sub #(.C(CFG_A)) sub (.din(a));
  Sub #(.C(CFG_A2)) sub_same (.din(a2));
  Sub #(.C(CFG_C)) sub_diff (.din(c));

  initial begin
    a = '0;
    b = '0;
    pkg = '0;
    cross_pkg = '0;
    a2 = '0;
    c = '0;
    `checkh($bits(a), 12);
    `checkh($bits(b), 15);
    `checkh($bits(pkg), 13);
    `checkh($bits(cross_pkg), 10);
    `checkh(P::cfg#(CFG_A)::COUNTERS, 4);
    `checkh(P::cfg#(CFG_B)::COUNTERS, 7);
    // Equal struct values must specialize identically, unequal ones distinctly.
    `checkh($bits(a2), $bits(a));
    `checkh(P::cfg#(CFG_A2)::COUNTERS, 4);
    `checkh(P::cfg#(CFG_C)::COUNTERS, 5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
