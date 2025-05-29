// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off UNUSEDSIGNAL */

module t_waive_no_module(
   input logic clk,
   input logic rst,
   input logic [7:0] abc
);
   // This module is not defined but we have waived it in the .vlt file.
   some_module_name #(
      .SOME_PARAM(1)
   ) u_some_module_name (
      .clk(clk),
      .rst(rst),
      .abc(abc)
   );
endmodule
