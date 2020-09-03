// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   initial begin
      if (task_as_func(1'b0)) $stop;
   end

   task task_as_func;
      input ign;
   endtask

endmodule
