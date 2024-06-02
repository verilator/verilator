// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

// Not legal to put "static" here, so no warning
function int f_dunit_static();
   int cnt = 0;  // Ok to require "static" here somehday
   return ++cnt;
endfunction

// Not legal to put "static" here, so no warning
task t_dunit_static();
   int cnt = 0;  // Ok to require "static" here somehday
   $display("%d", ++cnt);
endtask

task t_dunit_static_ok(input int in_ok = 1);
   static int cnt_ok = 0;  // No warning here
   $display("%d", ++cnt_ok);
endtask

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   function int f_implicit_static();
      int cnt = 0;
      return ++cnt;
   endfunction

   task t_implicit_static();
      int cnt = 0;
      $display("%d", ++cnt);
   endtask

   // verilator lint_off IMPLICITSTATIC
   function int f_implicit_but_lint_off();
      int cnt = 0;
      return ++cnt;
   endfunction

   input clk;

   int   a, b;
   initial begin
      a = f_dunit_static();
      t_dunit_static();
      t_dunit_static_ok();

      a = f_implicit_static();
      t_implicit_static();
      b = f_implicit_but_lint_off();
      $stop;
   end

endmodule
