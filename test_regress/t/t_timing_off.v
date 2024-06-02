// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   event e1;
   event e2;

   initial begin
       int x;
   // verilator timing_off
       #1
       fork @e1; @e2; join;
       @e1
       wait(x == 4)
       x = #1 8;
   // verilator timing_on
       if (x != 8) $stop;
       if ($time != 0) $stop;
   // verilator timing_off
       @e2;
   // verilator timing_on
       @e1;
       if ((e1.triggered && e2.triggered)
        || (!e1.triggered && !e2.triggered)) $stop;
       if ($time != 2) $stop;
       $write("*-* All Finished *-*\n");
       $finish;
   end

   initial #2 ->e1;
   // verilator timing_off
   initial #2 ->e2;
   // verilator timing_on
   initial #3 $stop; // timeout
   initial #1 @(e1, e2) #1 $stop; // timeout
endmodule
