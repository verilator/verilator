// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   bit failure;
   mutex check_bus(cyc, clk, failure);

   integer cyc_d1;
   always @ (posedge clk) cyc_d1 <= cyc;

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d cyc_d1=0x%0x  exp=%x failure=%x\n",
             $time, cyc, cyc_d1, $onehot0(cyc), failure);
`endif
      cyc <= cyc + 1;
      if (cyc < 3) begin
      end
      else if (cyc < 90) begin
         if (failure !== !$onehot0(cyc)) $stop;
      end
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

checker mutex (input logic [31:0] sig, input bit clk, output bit failure);
   logic [31:0] last_sig;
   assert property (@(negedge clk) $onehot0(sig))
     failure = 1'b0; else failure = 1'b1;
   assert property (@(negedge clk) sig == last_sig + 1);
   always_ff @(posedge clk) last_sig <= sig;
endchecker
