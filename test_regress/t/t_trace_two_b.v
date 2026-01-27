// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=1;
   integer c_trace_on;
   real    r;

   sub sub ();

   always @ (posedge clk) begin
      if (cyc != 0) begin
         r <= r + 0.1;
      end
   end
endmodule

module sub;
   integer inside_sub_a = 2;
endmodule
