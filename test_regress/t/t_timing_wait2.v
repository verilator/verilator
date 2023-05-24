// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   bit s[3:0] = {0, 0, 0, 0};

   initial begin
      wait (s[1]);
      s[0] = 1;
      $display("0");
   end

   initial begin
      wait (s[2]);
      s[1] = 1;
      $display("1");
      #1 $write("*-* All Finished *-*\n");
      $finish;
   end

   initial begin
      wait (s[3]);
      s[2] = 1;
      $display("2");
   end

   initial begin
      s[3] = 1;
   end

   initial #2 $stop;  // timeout
endmodule
