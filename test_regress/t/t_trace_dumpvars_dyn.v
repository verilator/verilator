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
   int   cyc;

   sub1 #(10) sub1a (.*);
   sub1 #(20) sub1b (.*);

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module sub1 #(parameter int ADD)
   (input int cyc);

   wire int value = cyc + ADD;

   sub2 #(ADD + 1) sub2a(.*);
   sub2 #(ADD + 2) sub2b(.*);
   sub2 #(ADD + 3) sub2c(.*);
endmodule

module sub2 #(parameter int ADD)
   (input int cyc);

   wire int value = cyc + ADD;
endmodule
