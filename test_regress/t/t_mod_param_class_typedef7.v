// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package pf;
  typedef struct packed {
    int unsigned CcNumTl;
    int unsigned PqSize;
  } cfg_t;
endpackage

virtual class xxx_class #(
    parameter pf::cfg_t Cfg
);
  typedef struct packed {
    logic [$clog2(Cfg.CcNumTl)-1:0] tl_index;
    logic [$clog2(Cfg.PqSize)-1:0] pq_index;
  } cmd_tag_t;
endclass

module mod2 #(
    parameter p_width = 16
) (
    output logic [p_width-1:0] q,
    input logic [p_width-1:0] d
);
  assign q = d;

  initial begin
    #1;
    `checkd(p_width, 7);
  end
endmodule

module top ();
  localparam pf::cfg_t Cfg0 = '{CcNumTl: 8, PqSize: 12};

  xxx_class#(Cfg0)::cmd_tag_t tag, tag_q;

  mod2 #($bits(tag)) t0 (
      tag_q,
      tag
  );

  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
