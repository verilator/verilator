// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   bit     a;
   bit     b;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         a <= '0;
         b <= '0;
      end
      else if (cyc == 10) begin
         a <= '1;
         b <= '1;
      end
      else if (cyc == 11) begin
         a <= '0;
         b <= '1;
      end
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   always_ff @(posedge clk) begin
      C1: cover property(a)
        begin
           // Assert under cover legal in some other simulators
           A2: assert (b);
        end
   end

endmodule
