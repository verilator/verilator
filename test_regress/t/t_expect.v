// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg   a;
   reg   b;

   initial begin
      #10;
      expect (@(posedge clk) a ##1 b) a = 110;
      #10;
      expect (@(posedge clk) a ##1 b) else a = 299;
      #10;
      expect (@(posedge clk) a ##1 b) a = 300; else a = 399;
   end

   // TODO set a/b appropriately - this is just a parsing test currently

endmodule
