// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (clk1, clk2);
   input wire clk1, clk2;
   logic b = 1'z === (clk1 & clk2);

   always begin
      if (!b) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
