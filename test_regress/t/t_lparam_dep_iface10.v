// DESCRIPTION: Verilator: Multiple interface instances with different params
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package scp;
  typedef struct packed {
    int unsigned ABits;
    int unsigned BBits;
  } cfg_t;
endpackage

interface a_if #(
  parameter a_p = 0
)();
  localparam int LP0 = a_p * 2;
  typedef logic [LP0-1:0] a_t;
endinterface

interface sc_if #(
  parameter scp::cfg_t cfg = 0
)();
  localparam int LP_MUL = cfg.ABits * cfg.BBits;
  localparam int LP_ADD = cfg.ABits + cfg.BBits;

  a_if #(LP_MUL) types_mul();
  a_if #(LP_ADD) types_add();
endinterface

module sc #(parameter scp::cfg_t cfg=0) (
  sc_if io
);

  typedef io.types_mul.a_t a_mul_t;
  typedef io.types_add.a_t a_add_t;

  initial begin
    #1;
    // cfg.ABits=2, cfg.BBits=3
    // LP_MUL=6 -> a_p=6 -> LP0=12 -> a_mul_t is 12 bits
    // LP_ADD=5 -> a_p=5 -> LP0=10 -> a_add_t is 10 bits
    `checkd($bits(a_mul_t), 12);
    `checkd($bits(a_add_t), 10);
  end
endmodule

module t();
  localparam scp::cfg_t sc_cfg = '{
    ABits : 2,
    BBits : 3
  };

  sc_if #(sc_cfg) sc_io ();

  sc #(sc_cfg) sc(
    .io(sc_io)
  );

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
