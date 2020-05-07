// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Duraid Madina.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   parameter logic [1:0] t0 [  2][  2] = '{'{2'd0, 2'd1}, '{2'd2, 2'd3}};
   parameter logic [1:0] t1 [0:1][0:1] = '{'{2'd0, 2'd1}, '{2'd2, 2'd3}};
   parameter logic [1:0] t2 [1:0][1:0] = '{'{2'd3, 2'd2}, '{2'd1, 2'd0}};

   always @ (posedge clk) begin
      if (t0[0][0] != t1[0][0]) $stop;
      if (t0[0][1] != t1[0][1]) $stop;
      if (t0[1][0] != t1[1][0]) $stop;
      if (t0[1][1] != t1[1][1]) $stop;
      if (t0[0][0] != t2[0][0]) $stop;
      if (t0[0][1] != t2[0][1]) $stop;
      if (t0[1][0] != t2[1][0]) $stop;
      if (t0[1][1] != t2[1][1]) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
