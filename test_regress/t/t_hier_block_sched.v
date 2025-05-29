// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t(clk);
   input clk;
   sub_0 sub_0(clk);
   sub_1 sub_1(clk);
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

import "DPI-C" context function void dpii_call();

module sub_0(input clk); /*verilator hier_block*/
   always @(posedge clk) dpii_call();
endmodule

module sub_1(input clk); /*verilator hier_block*/
   always @(posedge clk) dpii_call();
endmodule
