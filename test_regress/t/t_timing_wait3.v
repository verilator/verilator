// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0


module t;
   typedef process pr;
   pr p[4];
   int n = 0;

   initial begin
      wait (p[1]);
      p[1].await();
      p[0] = process::self();
      if (n == 3) n++;
      #2 $write("*-* All Finished *-*\n");
      $finish;
   end

   initial begin
      wait (p[2]);
      p[2].await();
      p[1] = process::self();
      if (n == 2) n++;
   end

   initial begin
      wait (p[3]);
      p[3].await();
      p[2] = process::self();
      if (n == 1) n++;
   end

   initial begin
      p[3] = process::self();
      if (n == 0) n++;
   end

   initial #1 if (n != 4) $stop;
   initial #3 $stop;  // timeout
endmodule
