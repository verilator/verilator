// DESCRIPTION: Verilator: Verilog Test module
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
    struct {logic [7:0] value;} arr[2];
    logic [7:0] mem[2];
    logic flag;
  } st_t;
  st_t s;
  logic [7:0] q;
  logic [7:0] m;
  assign q = s.arr[1].value;
  assign m = s.mem[1];

  initial begin
    s.arr[0].value = 8'h01;
    s.arr[1].value = 8'h5a;
    s.mem[0] = 8'h02;
    s.mem[1] = 8'h03;
    s.flag = 1'b0;
    // Force outside of the arrays
    force s.flag = 1'b1;
    #1;
    `checkh(q, 8'h5a);
    `checkh(m, 8'h03);
    `checkh(s.flag, 1'b1);
    // Force inside of the arrays
    force s.arr[1].value = 8'ha5;
    force s.mem[1] = 8'h30;
    s.arr[1].value = 8'h66;
    #1;
    `checkh(q, 8'ha5);
    `checkh(m, 8'h30);
    `checkh(s.arr[0].value, 8'h01);
    `checkh(s.mem[0], 8'h02);
    `checkh(s.flag, 1'b1);
    release s.arr[1].value;
    release s.mem[1];
    #1;
    `checkh(q, 8'ha5);
    `checkh(m, 8'h30);
    s.arr[1].value = 8'h67;
    s.mem[1] = 8'h04;
    #1;
    `checkh(q, 8'h67);
    `checkh(m, 8'h04);
    `checkh(s.flag, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
