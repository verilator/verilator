// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   function int f1;
      #1 $stop;
      f1 = 0;
   endfunction

   function int f2;
      f2 = #5 0; $stop;
   endfunction

   event e;
   function int f3;
      @e $stop;
      f3 = 0;
   endfunction

   function int f4;
      f4 = @e 0; $stop;
   endfunction

   int i;

   function int f5;
      wait(i == 0) $stop;
      f5 = 0;
   endfunction

   initial begin
      i = f1();
      $write("*-* All Finished *-*\n");
      $finish;
   end

   final begin
      #1;
      $stop;
   end

endmodule
