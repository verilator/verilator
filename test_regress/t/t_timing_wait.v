// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(msg) $write(msg)
`else
 `define WRITE_VERBOSE(msg)
`endif

module t;
   int a = 0;
   int b = 0;
   int c = 0;

   initial begin
      `WRITE_VERBOSE("start with a==0, b==0, c==0\n");
      #2 a = 1; `WRITE_VERBOSE("assign 1 to a\n");
      #1 a = 2; `WRITE_VERBOSE("assign 2 to a\n");  // a==2
      #1 a = 0; `WRITE_VERBOSE("assign 0 to a\n");
      #1 a = 2; `WRITE_VERBOSE("assign 2 to a\n");  // 1<a<3
      #1 b = 2; `WRITE_VERBOSE("assign 2 to b\n");
      #1 a = 1; `WRITE_VERBOSE("assign 1 to a\n");  // b>a
      #1 c = 3; `WRITE_VERBOSE("assign 3 to c\n");
      #1 c = 4; `WRITE_VERBOSE("assign 4 to c\n");  // a+b<c
      #1 c = 4; `WRITE_VERBOSE("assign 5 to b\n");  // a<b && b>c
      b = 5;
   end

   initial begin
      #1 `WRITE_VERBOSE("waiting for a==2\n");
      wait(a == 2) if (a != 2) $stop;
      `WRITE_VERBOSE("waiting for a<2\n");
      wait(a < 2) if (a >= 2) $stop;
      `WRITE_VERBOSE("waiting for a==0\n");
      wait(a == 0) if (a != 0) $stop;
      `WRITE_VERBOSE("waiting for 1<a<3\n");
      wait(a > 1 && a < 3) if (a <= 1 || a >= 3) $stop;
      `WRITE_VERBOSE("waiting for b>a\n");
      wait(b > a) if (b <= a) $stop;
      `WRITE_VERBOSE("waiting for a+b<c\n");
      wait(a + b < c) if (a + b >= c) $stop;
      `WRITE_VERBOSE("waiting for a<b && b>c\n");
      wait(a < b && b > c) if (a >= b || b <= c) $stop;

      wait(1);

      wait(0 < 1) $write("*-* All Finished *-*\n");
      $finish;
   end

   initial wait(0) $stop;
   initial wait(1 == 0) $stop;

   initial #11 $stop; // timeout
endmodule
