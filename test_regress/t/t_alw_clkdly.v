// DESCRIPTION::Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Krzysztof Bieganski.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic other;

   integer cyc = 1;

   always @(posedge clk) begin
      $write("@ posedge clk\n");
      other <= ~other;
      cyc++;
      if (cyc == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   always @(other) begin
       $write("@ anyedge other\n");
   end

endmodule
