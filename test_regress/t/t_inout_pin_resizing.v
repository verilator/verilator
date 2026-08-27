// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// verilator lint_off WIDTHTRUNC
// verilator lint_off REALCVT

module t;
  real src_r;

  bit unsigned [7:0] src_u2;
  bit signed [7:0] src_s2;
  real dst_r;

  task cp_u2(output bit unsigned [7:0] dst, input bit unsigned [7:0] src);
    dst = src;
  endtask

  task cp_s2(output bit signed [7:0] dst, input bit signed [7:0] src);
    dst = src;
  endtask

  task cp_io_u2(inout bit unsigned [7:0] io, input bit unsigned [7:0] src);
    io = io + src;
  endtask

  task cp_io_s2(inout bit signed [7:0] io, input bit signed [7:0] src);
    io = io + src;
  endtask

  initial begin
    src_u2 = 7;
    cp_u2(dst_r, src_u2);
    `checkr(dst_r, 7.0);

    src_s2 = -7;
    cp_s2(dst_r, src_s2);
    `checkr(dst_r, -7.0);

    src_u2 = 7;
    dst_r = 5.0;
    cp_io_u2(dst_r, src_u2);
    `checkr(dst_r, 12.0);

    src_s2 = -7;
    dst_r = -3.0;
    cp_io_s2(dst_r, src_s2);
    `checkr(dst_r, -10.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
