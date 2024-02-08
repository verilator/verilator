// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);

   int a, b;
   int sum;
   // Complicated assignment cases

   initial begin
      sum = 0;
      for (integer a=0; a<3; ) begin
         a = a + 1;
         sum = sum + a;
      end
      `checkd(sum, 6);

      // foperator_assignment
      sum = 0;
      for (integer a=0; a<3; a=a+1, sum += a) ;
      `checkd(sum, 6);

      // inc_or_dec_expression
      sum = 0;
      for (integer a=0; a<3; a++, ++sum) ;
      `checkd(sum, 3);

      // task_subroutine_call
      sum = 0;
      for (integer a=0; a<3; a++, sum += $clog2(a)) ;
      `checkd(sum, 3);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
