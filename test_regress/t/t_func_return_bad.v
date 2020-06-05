// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   task t1;
      return 1;  // Shouldn't return value
   endtask
   function int f1;
      return;  // Should return value
   endfunction

   initial begin
      return;  // Not under function
      continue;  // Not under loop
      break;  // Not under loop
      begin : foo
      end
      disable foo;  // Disabling outside block
   end
endmodule
