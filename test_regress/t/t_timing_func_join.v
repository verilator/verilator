// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);
   function int fun(int val);
      fork
         $display("abc");
         $display("def");
      join_none  // Although join is illegal, join_none legal (IEEE 1800-2023 13.4)
      return val + 2;
   endfunction

   task tsk();
      fork
         $display("ghi");
         $display("jkl");
      join_none
   endtask

   initial begin
      $display("$d", fun(2));
      tsk();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
