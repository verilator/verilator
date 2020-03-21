// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "t_flag_f_tsub_inc.v"

module t;
   initial begin
`ifndef GOT_DEF1
      $write("%%Error: NO GOT_DEF1\n"); $stop;
`endif
`ifndef GOT_DEF2
      $write("%%Error: NO GOT_DEF2\n"); $stop;
`endif
`ifndef GOT_DEF3
      $write("%%Error: NO GOT_DEF3\n"); $stop;
`endif
`ifndef GOT_DEF4
      $write("%%Error: NO GOT_DEF4\n"); $stop;
`endif
`ifndef GOT_DEF5
      $write("%%Error: NO GOT_DEF5\n"); $stop;
`endif
`ifndef GOT_DEF6
      $write("%%Error: NO GOT_DEF6\n"); $stop;
`endif
`ifdef NON_DEF
      $write("%%Error: NON_DEF\n"); $stop;
`endif
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
