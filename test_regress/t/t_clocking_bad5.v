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

   sub sub(.*);

   // Bad - no global clock
   always @ ($global_clock) $display;

endmodule

module sub(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   global clocking ck @(posedge clk); endclocking

   // Bad - global duplicate
   global clocking ogck @(posedge clk); endclocking

   // Bad - name duplicate
   global clocking ck @(posedge clk); endclocking

endmodule
