// DESCRIPTION: Verilator: Verilog Test module
//
// Asserts that a struct signal marked externally forceable can also be the
// target of a procedural 'force' on one of its members: the model elaborates
// and compiles, the forced member and the forced element of an unpacked-array
// member read back forced, and sibling fields are unaffected.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;

  typedef struct {
    logic [7:0] arr[4];
    logic [7:0] a;
    logic [7:0] b;
  } st_t;

  st_t s  /*verilator forceable*/;

  initial begin
    for (int i = 0; i < 4; ++i) s.arr[i] = 8'h10 + 8'(i);
    s.a = 8'h01;
    s.b = 8'h02;
    #1;
    `checkh(s.a, 8'h01);

    force s.a = 8'haa;
    #1;
    `checkh(s.a, 8'haa);
    `checkh(s.b, 8'h02);
    `checkh(s.arr[2], 8'h12);

    force s.arr[2] = 8'hbb;
    #1;
    `checkh(s.arr[2], 8'hbb);
    `checkh(s.a, 8'haa);
    `checkh(s.b, 8'h02);
    `checkh(s.arr[1], 8'h11);

    release s.a;
    release s.arr[2];
    #1;
    `checkh(s.a, 8'haa);
    `checkh(s.arr[2], 8'hbb);

    s.a = 8'h55;
    s.arr[2] = 8'h66;
    #1;
    `checkh(s.a, 8'h55);
    `checkh(s.arr[2], 8'h66);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
