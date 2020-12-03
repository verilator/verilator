// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Rafal Kapuscik
// SPDX-License-Identifier: CC0-1.0
//

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   bit [3:0] addr;
   initial begin
      super.addr = 2;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
