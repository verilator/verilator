// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class xxx_class #(
    parameter int X = 1
);
  typedef logic [X-1:0] cmd_tag_t;
endclass

module mod_a #(
    parameter p_width = 16
) ();
endmodule

module the_top ();
  xxx_class#(16)::cmd_tag_t tag;
  mod_a #($bits(tag)) t0 ();

  initial begin
    #2;
    `checkd($bits(tag), 16);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
