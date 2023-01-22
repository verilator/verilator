// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

function int f_implicit_static();
   int cnt = 0;
   return ++cnt;
endfunction

task t_implicit_static();
   int cnt = 0;
   $display("%d", ++cnt);
endtask


module t (/*AUTOARG*/
   // Inputs
   clk
   );

   // verilator lint_off IMPLICITSTATIC
   function int f_implicit_but_lint_off();
      int cnt = 0;
      return ++cnt;
   endfunction

   input clk;

   int   a, b;
   initial begin
      a = f_implicit_static();
      t_implicit_static();
      b = f_implicit_but_lint_off();
      $stop;
   end

endmodule
