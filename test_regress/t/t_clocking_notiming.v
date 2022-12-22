// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic clk;
   logic out;
   clocking cb @(posedge clk);
       output #1 out;
   endclocking
endmodule
