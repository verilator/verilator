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

   global clocking cb @(posedge clk);
       input #1 output #1step x;
       inout y;
       output posedge #1 a;
       output negedge #1 b;
       output edge #1 b;
   endclocking

   global clocking @(posedge clk);
   endclocking
endmodule
