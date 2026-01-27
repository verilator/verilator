// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ms/1ms

// See also t_time_sc_*.v/pl

module t
  (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer    cyc; initial cyc = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
