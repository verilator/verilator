// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   clocking cb @(posedge clk);
       output posedge #1 a;
       output negedge #1 b;
       output edge #1 b;
   endclocking

endmodule
