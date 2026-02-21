// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// DESCRIPTION:
// Minimal testcase for depgraph interface typedef resolution through
// interface ports connected to specialized interface instances.
//

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package acme_pkg;
  typedef struct packed {
    int DataBits;
  } cfg_t;
endpackage

interface acme_if #(parameter acme_pkg::cfg_t cfg = '0)();
  typedef logic [cfg.DataBits-1:0] data_t;
endinterface

module child(acme_if io, output int width_o);
  typedef io.data_t data_t;
  data_t payload;
  assign width_o = $bits(data_t);
endmodule

module top;
  localparam acme_pkg::cfg_t cfg0 = '{DataBits:32};
  localparam acme_pkg::cfg_t cfg1 = '{DataBits:64};

  acme_if #(cfg0) io0();
  acme_if #(cfg1) io1();

  int width0;
  int width1;

  child u0(.io(io0), .width_o(width0));
  child u1(.io(io1), .width_o(width1));

  initial begin
    #1;
    `checkd(width0, 32);
    `checkd(width1, 64);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
