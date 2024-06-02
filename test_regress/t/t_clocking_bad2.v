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

   logic in, out;
   clocking cb @(posedge clk);
       default input #1 output #1step;
       default input #2 output #2;
       output #1step out;
       output out;
   endclocking
endmodule
