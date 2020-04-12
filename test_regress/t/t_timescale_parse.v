// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//verilator lint_off REALCVT

`define testmod(modname) \
module modname; \
  time t; \
    task check; t = 1ns; $write("%m %0t\n", t); endtask \
endmodule

`timescale 1s/1fs
`testmod(s0)
`timescale 100ms/1fs
`testmod(s1)
`timescale 10ms/1fs
`testmod(s2)
`timescale 1ms/1fs
`testmod(s3)
`timescale 100us/1fs
`testmod(s4)
`timescale 10us/1fs
`testmod(s5)
`timescale 1us/1fs
`testmod(s6)
`timescale 100ns/1fs
`testmod(s7)
`timescale 10ns/1fs
`testmod(s8)
`timescale 1ns/1fs
`testmod(s9)
`timescale 100ps/1fs
`testmod(s10)
`timescale 10ps/1fs
`testmod(s11)
`timescale 1ps/1fs
`testmod(s12)
`timescale 100 fs/1fs
`testmod(s13)
`timescale 10fs/1 fs
`testmod(s14)
`timescale 1 fs / 1 fs  // Comment
`testmod(s15)


module r0;
   timeunit 10ns / 1ns;
   task check; $write("%m %0t\n", $time); endtask
endmodule

module r1;
   timeunit 10ns;
   timeprecision 1ns;
   task check; $write("%m %0t\n", $time); endtask
endmodule

module t;
   s0 s0();
   s1 s1();
   s2 s2();
   s3 s3();
   s4 s4();
   s5 s5();
   s6 s6();
   s7 s7();
   s8 s8();
   s9 s9();
   s10 s10();
   s11 s11();
   s12 s12();
   s13 s13();
   s14 s14();
   s15 s15();

   r0 r0();
   r1 r1();

   final begin
      s0.check();
      s1.check();
      s2.check();
      s3.check();
      s4.check();
      s5.check();
      s6.check();
      s7.check();
      s8.check();
      s9.check();
      s10.check();
      s11.check();
      s12.check();
      s13.check();
      s14.check();
      s15.check();
      r0.check();
      r1.check();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
