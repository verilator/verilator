// DESCRIPTION: Verilator: 3-level nested interface typedef with dependent localparams
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

// Level 3: innermost interface
interface a_if #(
  parameter a_p = 0
)();
  localparam int LP0 = a_p * 2;
  typedef logic [LP0-1:0] a_t;
endinterface

// Level 2: middle interface
interface sct_if #(
  parameter scp::cfg_t cfg = 0
)();
  localparam int LP0 = cfg.ABits * cfg.BBits;
  a_if #(LP0) a_if0();
  typedef a_if0.a_t a_t;
endinterface

// Level 1: outermost interface
interface sc_if #(
  parameter scp::cfg_t cfg = 0
)();
  sct_if #(cfg) types();
  typedef types.a_t a_t;
endinterface

module sc #(parameter scp::cfg_t cfg=0) (
  sc_if io
);

  typedef io.a_t a_t;

  initial begin
    #1;
    // cfg.ABits=2, cfg.BBits=3 -> LP0=6 -> a_p=6 -> LP0=12 -> a_t is 12 bits
    `checkd(12, $bits(a_t));
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
