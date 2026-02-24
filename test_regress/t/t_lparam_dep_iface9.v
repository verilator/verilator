// DESCRIPTION: Verilator: Multiple dependent localparams in chain
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

// Interface with chained localparam dependencies
interface a_if #(
  parameter a_p = 0
)();
  localparam int LP0 = a_p * 2;      // LP0 = a_p * 2
  localparam int LP1 = LP0 + 1;      // LP1 = LP0 + 1
  localparam int LP2 = LP1 * LP0;    // LP2 = LP1 * LP0
  typedef logic [LP2-1:0] a_t;
endinterface

interface sc_if #(
  parameter scp::cfg_t cfg = 0
)();
  localparam int LP0 = cfg.ABits * cfg.BBits;
  a_if #(LP0) types();
endinterface

module sc #(parameter scp::cfg_t cfg=0) (
  sc_if io
);

  typedef io.types.a_t a_t;

  initial begin
    #1;
    // cfg.ABits=2, cfg.BBits=3 -> LP0=6
    // a_if: a_p=6 -> LP0=12, LP1=13, LP2=156 -> a_t is 156 bits
    `checkd(156, $bits(a_t));
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
