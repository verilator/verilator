// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   reg [31:0] dly0;

   // DFG can fold this into 'dly3 = dly1 = dly0 + 1' and 'dly2 = dly0 + 2',
   // but the 'dly0 + 1' term having multiple sinks needs to considered.
   wire [31:0] dly1 = dly0 + 32'h1;
   wire [31:0] dly2 = dly1 + 32'h1;
   wire [31:0] dly3 = dly0 + 32'h1;

   always @ (posedge clk) begin
      $display("[%0t] dly0=%h dly1=%h dly2=%h dly3=%h", $time, dly0, dly1, dly2, dly3);
      cyc <= cyc + 1;
      if (cyc == 1) begin
         dly0 <= 32'h55;
      end
      else if (cyc == 3) begin
         if (dly1 !== 32'h56) $stop;
         if (dly2 !== 32'h57) $stop;
         if (dly3 !== 32'h56) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
