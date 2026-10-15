// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2004 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); fail=1; end while(0)
// verilog_format: on

module t;

  bit fail;

  reg [7:0] a8;
  reg [6:0] a7;
  reg signed [7:0] s8;
  reg signed [63:0] qs64;
  reg [63:0] q64;
  reg [32:0] q33;

  // IEEE says for ** the size is L(i).  Thus Icarus Verilog is wrong in sizing some of the below.

  initial begin
    // verilog_format: off
    `checkh( (64'b1111 ** 64'b1110),  64'h67b6cfc1b29a21);
`ifndef NC
    `checkh( (-4'd1 ** -4'sd2),       4'h0);  //bug730
`endif
`ifndef VCS
    `checkh( (-4'd1 ** -4'd2),                4'h1);
    `checkh( (4'd15 ** 4'd14),                4'h1);
`endif
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
    `checkh(( 8'h1  **  8'sh3),  8'h1  );  // 1
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

`ifndef NC
    `checkh((-8'sh3 ** -8'sh3),  8'h0 );  // 0 (a<-1)
`endif
`ifndef IVERILOG
`ifndef QUESTA
`ifndef VCS
    `checkh((-8'sh1 ** -8'sh2),  8'h1 );  // -1^odd=-1, -1^even=1
    `checkh((-8'sh1 ** -8'sh3),  8'hff);  // -1^odd=-1, -1^even=1
`endif
`endif
`endif
//    `checkh(( 8'h0  ** -8'sh3),  8'hx );  // x
    `checkh(( 8'h1  ** -8'sh3),  8'h1 );  // 1**b always 1
`ifndef NC
    `checkh(( 8'h3  ** -8'sh3),  8'h0 );  // 0
    `checkh(( 8'sh3 ** -8'sh3),  8'h0 );  // 0
`endif
    // verilog_format: on

    // The left operand is context determined, so the result width of an assignment applies to
    // it, including nested powers, and ** is right associative
    a8 = 8'd4;
    a7 = 7'd5;
    // verilator lint_off WIDTHEXPAND
    q64 = a8 ** 4 ** 1;
    `checkh(q64, 64'h100);
    q64 = a8 ** (4 ** 1);
    `checkh(q64, 64'h100);
    q64 = (a8 ** 4) ** 1;
    `checkh(q64, 64'h100);
    q64 = a8 ** 2 ** 2 ** 1;
    `checkh(q64, 64'h100);
    q33 = a7 ** 3 ** 1;
    `checkh(q33, 33'd125);
    s8 = -8'sd2;
    qs64 = s8 ** 3 ** 1;
    `checkh(qs64, -64'sd8);
    // verilator lint_on WIDTHEXPAND

    if (fail) $stop;
    else $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
