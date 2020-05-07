// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

module sub
  (
   input clk,
   input reset_l
   );

   // Example counter/flop
   reg [31:0] count_c;
   always_ff @ (posedge clk) begin
      if (!reset_l) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         count_c <= 32'h0;
         // End of automatics
      end
      else begin
         count_c <= count_c + 1;
         if (count_c >= 3) begin
            // This write is a magic value the Makefile uses to make sure the
            // test completes successfully.
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

   // An example assertion
   always_ff @ (posedge clk) begin
      AssertionExample: assert (!reset_l || count_c<100);
   end

   // And example coverage analysis
   cover property (@(posedge clk) count_c==3);

endmodule
