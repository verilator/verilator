// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   reg a;
   initial begin
      $unknown_sys_task_call_to_be_bbox("blah");
      $unkown_sys_task_call_noarg;
      a = $unknown_sys_func_call(23);
      a = $unknown_sys_func_call_noarg;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
