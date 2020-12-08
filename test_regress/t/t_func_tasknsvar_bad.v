// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   task foo(inout sig);
      sig = '1;
   endtask

   reg [3:0] bus_we_select_from;

   initial begin
      foo(bus_we_select_from[2]);  // Will get TASKNSVAR error
   end

endmodule
