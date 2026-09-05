// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog
//
// Assignment compatibility test.
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
  logic [  0:0]  s0;
  logic [  7:0]  s1;
  logic [  8:0]  s2;
  logic [ 31:0]  s3;
  logic [ 32:0]  s4;
  logic [ 63:0]  s5;
  logic [ 64:0]  s6;
  logic [127:0]  s7;
  logic [128:0]  s8;
  logic [255:0]  s9;
  logic [256:0] s10;
  logic [300:0] s11;
  bit   [ 13:0] foo;
  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
    #10;
      s0  = 1;
      s1  = 1;
      s2  = 1;
      s3  = 1;
      s4  = 1;
      s5  = 1;
      s6  = 1;
      s7  = 1;
      s8  = 1;
      s9  = 1;
      s10 = 1;
      s11 = 1;
      foo = 1;
    #10
      s0  = 0;
      s1  = 0;
      s2  = 0;
      s3  = 0;
      s4  = 0;
      s5  = 0;
      s6  = 0;
      s7  = 0;
      s8  = 0;
      s9  = 0;
      s10 = 0;
      s11 = 0;
      foo = 0;
    #10
      s0  = 'z;
      s1  = 'z;
      s2  = 'z;
      s3  = 'z;
      s4  = 'z;
      s5  = 'z;
      s6  = 'z;
      s7  = 'z;
      s8  = 'z;
      s9  = 'z;
      s10 = 'z;
      s11 = 'z;
      foo = 'z;
    #10
      s0  = 'x;
      s1  = 'x;
      s2  = 'x;
      s3  = 'x;
      s4  = 'x;
      s5  = 'x;
      s6  = 'x;
      s7  = 'x;
      s8  = 'x;
      s9  = 'x;
      s10 = 'x;
      s11 = 'x;
      foo = 'x;
  #10 $finish;
  end
endmodule
