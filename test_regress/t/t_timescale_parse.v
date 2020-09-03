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

`timescale 100s/1fs
`testmod(sp2)
`timescale 10s/1fs
`testmod(sp1)
`timescale 1s/1fs
`testmod(sp0)
`timescale 100ms/1fs
`testmod(sm1)
`timescale 10ms/1fs
`testmod(sm2)
`timescale 1ms/1fs
`testmod(sm3)
`timescale 100us/1fs
`testmod(sm4)
`timescale 10us/1fs
`testmod(sm5)
`timescale 1us/1fs
`testmod(sm6)
`timescale 100ns/1fs
`testmod(sm7)
`timescale 10ns/1fs
`testmod(sm8)
`timescale 1ns/1fs
`testmod(sm9)
`timescale 100ps/1fs
`testmod(sm10)
`timescale 10ps/1fs
`testmod(sm11)
`timescale 1ps/1fs
`testmod(sm12)
`timescale 100 fs/1fs
`testmod(sm13)
`timescale 10fs/1 fs
`testmod(sm14)
`timescale 1 fs / 1 fs  // Comment
`testmod(sm15)


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
   sp2 sp2();
   sp1 sp1();
   sp0 sp0();
   sm1 sm1();
   sm2 sm2();
   sm3 sm3();
   sm4 sm4();
   sm5 sm5();
   sm6 sm6();
   sm7 sm7();
   sm8 sm8();
   sm9 sm9();
   sm10 sm10();
   sm11 sm11();
   sm12 sm12();
   sm13 sm13();
   sm14 sm14();
   sm15 sm15();

   r0 r0();
   r1 r1();

   final begin
      sp2.check();
      sp1.check();
      sp0.check();
      sm1.check();
      sm2.check();
      sm3.check();
      sm4.check();
      sm5.check();
      sm6.check();
      sm7.check();
      sm8.check();
      sm9.check();
      sm10.check();
      sm11.check();
      sm12.check();
      sm13.check();
      sm14.check();
      sm15.check();
      r0.check();
      r1.check();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
