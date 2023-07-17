// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0


module t;
   typedef process pr;
   pr p[] = new[4];

   initial begin
      wait (p[1]);
      p[1].await();
      p[0] = process::self();
      $display("0");
      #1 $write("*-* All Finished *-*\n");
      $finish;
   end

   initial begin
      wait (p[2]);
      p[2].await();
      p[1] = process::self();
      $display("1");
   end

   initial begin
      wait (p[3]);
      p[3].await();
      p[2] = process::self();
      $display("2");
   end

   initial begin
      p[3] = process::self();
   end

   initial #2 $stop;  // timeout
endmodule
