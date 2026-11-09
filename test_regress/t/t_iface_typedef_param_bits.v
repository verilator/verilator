// DESCRIPTION: Verilator: Verilog Test module
//
// Sizes of a type from a parameterized interface must use the specialized
// parameter, not the value the interface was declared with.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package a_pkg;
  typedef struct packed {int unsigned p_a;} cfg_t;
endpackage

interface sub_if #(
    parameter a_pkg::cfg_t cfg = '{p_a: 7}
);
  typedef logic [cfg.p_a-1:0] data_t;
  typedef struct packed {
    logic [3:0] addr;
    data_t data;
  } data2_t;

  localparam int DBITS = $bits(data_t);
  localparam int DHIGH = $high(data_t);
  localparam int DLOW = $low(data_t);
  localparam int DLEFT = $left(data_t);
  localparam int DRIGHT = $right(data_t);
  localparam int DSIZE = $size(data_t);
  localparam int DINCR = $increment(data_t);
endinterface

module sub (
    sub_if io
);
endmodule

module t ();
  parameter a_pkg::cfg_t cfg = '{p_a: 16};

  sub_if #(cfg) sub_io ();
  sub_if #('{p_a: 33}) wide_io ();
  sub_if default_io ();

  sub u_sub (.io(sub_io));

  typedef sub_io.data2_t data2_t;
  typedef sub_io.data_t data_t;

  localparam int COUNT = $bits(data2_t);
  localparam int DBITS = $bits(data_t);
  localparam int DHIGH = $high(data_t);
  localparam int DLOW = $low(data_t);
  localparam int DLEFT = $left(data_t);
  localparam int DRIGHT = $right(data_t);
  localparam int DSIZE = $size(data_t);
  localparam int DINCR = $increment(data_t);

  initial begin
    if (COUNT != 20) $stop;
    if (DBITS != 16) $stop;
    if (DHIGH != 15) $stop;
    if (DLOW != 0) $stop;
    if (DLEFT != 15) $stop;
    if (DRIGHT != 0) $stop;
    if (DSIZE != 16) $stop;
    if (DINCR != 1) $stop;
    `checkd(sub_io.DBITS, 16);
    `checkd(sub_io.DHIGH, 15);
    `checkd(sub_io.DLOW, 0);
    `checkd(sub_io.DLEFT, 15);
    `checkd(sub_io.DRIGHT, 0);
    `checkd(sub_io.DSIZE, 16);
    `checkd(sub_io.DINCR, 1);
    `checkd(wide_io.DBITS, 33);
    `checkd(wide_io.DHIGH, 32);
    `checkd(wide_io.DLOW, 0);
    `checkd(wide_io.DLEFT, 32);
    `checkd(wide_io.DRIGHT, 0);
    `checkd(wide_io.DSIZE, 33);
    `checkd(wide_io.DINCR, 1);
    `checkd(default_io.DBITS, 7);
    `checkd(default_io.DHIGH, 6);
    `checkd(default_io.DLOW, 0);
    `checkd(default_io.DLEFT, 6);
    `checkd(default_io.DRIGHT, 0);
    `checkd(default_io.DSIZE, 7);
    `checkd(default_io.DINCR, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
