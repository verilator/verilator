// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package foo_pkg;
   function int foo_func;
      input int b;
      int b_current;
      return 0;
   endfunction
endpackage

module sub;
   int a = 1212;
endmodule

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   int cyc;

   import foo_pkg::*;

   sub sub();

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
