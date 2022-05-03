// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); fail=1; end while(0)

module t (/*AUTOARG*/);

   bit fail;

   // IEEE says for ** the size is L(i).  Thus Icarus Verilog is wrong in sizing some of the below.

   initial begin
      // NC=67b6cfc1b29a21  VCS=c1b29a20(wrong)   IV=67b6cfc1b29a21  Verilator=67b6cfc1b29a21
      $display("15 ** 14    = %0x  expect 67b6cfc1b29a21", 64'b1111 ** 64'b1110);
      // NC=1   VCS=0  IV=0   Verilator=1 (wrong,fixed)
      $display("15 **-4'sd2 = %0x expect 0 (per IEEE negative power)", ((-4'd1 ** -4'sd2)));
      // NC=1   VCS=0  IV=67b6cfc1b29a21(wrong)  Verilator=1
      $display("15 ** 14    = %0x expect 1 (LSB 4-bits of 67b6cfc1b29a21)", ((-4'd1 ** -4'd2)));
      // NC=1   VCS=0  IV=67b6cfc1b29a21(wrong)  Verilator=1
      $display("15 ** 14    = %0x expect 1 (LSB 4-bits of 67b6cfc1b29a21)", ((4'd15 ** 4'd14)));
      // NC=8765432187654321  VCS=8765432187654000(wrong) IV=8765432187654321   Verilator=8765432187654321
      $display("64'big ** 1 = %0x  expect %0x", 64'h8765432187654321 ** 1, 64'h8765432187654321);
      $display("\n");

      `checkh( (64'b1111 ** 64'b1110),  64'h67b6cfc1b29a21);
      `checkh( (-4'd1 ** -4'sd2),       4'h0);  //bug730
      `checkh( (-4'd1 ** -4'd2),                4'h1);
      `checkh( (4'd15 ** 4'd14),                4'h1);
      `checkh( (64'h8765432187654321 ** 4'h1), 64'h8765432187654321);

      `checkh((-8'sh3 **  8'h3) ,  8'he5 );  // a**b  (-27)
      `checkh((-8'sh1 **  8'h2) ,  8'h1  );  // -1^odd=-1, -1^even=1
      `checkh((-8'sh1 **  8'h3) ,  8'hff );  // -1^odd=-1, -1^even=1
      `checkh(( 8'h0  **  8'h3) ,  8'h0  );  // 0
      `checkh(( 8'h1  **  8'h3) ,  8'h1  );  // 1
      `checkh(( 8'h3  **  8'h3) ,  8'h1b );  // a**b (27)
      `checkh(( 8'sh3 **  8'h3) ,  8'h1b );  // a**b (27)
      `checkh(( 8'h6  **  8'h3) ,  8'hd8 );  // a**b (216)
      `checkh(( 8'sh6 **  8'h3) ,  8'hd8 );  // a**b (216)

      `checkh((-8'sh3 **  8'sh3),  8'he5 );  // a**b
      `checkh((-8'sh1 **  8'sh2),  8'h1  );  // -1^odd=-1, -1^even=1
      `checkh((-8'sh1 **  8'sh3),  8'hff );  // -1^odd=-1, -1^even=1
      `checkh(( 8'h0  **  8'sh3),  8'h0  );  // 0
      `checkh(( 8'h1  **  8'sh3),  8'h1  );   // 1
      `checkh(( 8'h3  **  8'sh3),  8'h1b );  // a**b (27)
      `checkh(( 8'sh3 **  8'sh3),  8'h1b );  // a**b (27)
      `checkh(( 8'h6  **  8'sh3),  8'hd8 );  // a**b (216)
      `checkh(( 8'sh6 **  8'sh3),  8'hd8 );  // a**b (216)

      `checkh((-8'sh3 ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh((-8'sh1 ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh((-8'sh1 ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh(( 8'h0  ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh(( 8'h1  ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh(( 8'h3  ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh(( 8'sh3 ** -8'sh0),  8'h1 );  // a**0 always 1

      `checkh((-8'sh3 ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh((-8'sh1 ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh((-8'sh1 ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh(( 8'h0  ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh(( 8'h1  ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh(( 8'h3  ** -8'sh0),  8'h1 );  // a**0 always 1
      `checkh(( 8'sh3 ** -8'sh0),  8'h1 );  // a**0 always 1

      `checkh((-8'sh3 ** -8'sh3),  8'h0 );  // 0 (a<-1)    // NCVERILOG bug
      `checkh((-8'sh1 ** -8'sh2),  8'h1 );  // -1^odd=-1, -1^even=1
      `checkh((-8'sh1 ** -8'sh3),  8'hff);  // -1^odd=-1, -1^even=1
//    `checkh(( 8'h0  ** -8'sh3),  8'hx );  // x  // NCVERILOG bug
      `checkh(( 8'h1  ** -8'sh3),  8'h1 );  // 1**b always 1
      `checkh(( 8'h3  ** -8'sh3),  8'h0 );  // 0  // NCVERILOG bug
      `checkh(( 8'sh3 ** -8'sh3),  8'h0 );  // 0  // NCVERILOG bug


      if (fail) $stop;
      else $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
