// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit unsigned [3:0] dst_u2s;
  bit signed [3:0] dst_s2s;
  bit unsigned [11:0] dst_u2l;
  bit signed [11:0] dst_s2l;

  real src_r;

  task cp_r(output real dst, input real src);
    dst = src;
  endtask

  initial begin
    src_r = -7.0;
    cp_r(dst_u2s, src_r);
    `checkh(dst_u2s, 4'h9);
    cp_r(dst_s2s, src_r);
    `checkh(dst_s2s, -7);
    cp_r(dst_u2l, src_r);
    `checkh(dst_u2l, 12'hff9);
    cp_r(dst_s2l, src_r);
    `checkh(dst_s2l, -7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
