// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   bit clk;
   int a, b;

   always #10 clk = ~clk;

   initial begin
      $monitor("[%0t] a=%0d b=%0d", $time, a, b);
      #1;  // So not on clock edge
      #100;
      a = 10;
      #10;
      b = 20;
      #10;
      a = 11;
      #10;
      b = 22;
      #100;
      #10;
      $monitoroff;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
