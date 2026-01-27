// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;

   event e1;
   event e2;
   int v = 0;

   initial begin
     #1 $strobe("v = %0d", v); ->e1;
     @e2 $strobe("v = %0d", v); ->e1;
     @e2 $strobe("v = %0d", v); ->e1;
     @e2 $write("*-* All Finished *-*\n");
     $finish;
   end

   initial begin
     @e1 v = 1; #1 ->e2;
     @e1 v = 2; #1 ->e2;
     @e1 v = 3; #1 ->e2;
   end

   initial #5 $stop; // timeout
endmodule
