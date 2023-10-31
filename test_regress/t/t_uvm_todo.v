// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define UVM_NO_DPI

`include "t_uvm_pkg_todo.vh"

module t(/*AUTOARG*/);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
