// DESCRIPTION: Verilator: Verilog Test module
//
// Sizes of a type from a parameterized interface must use the specialized
// parameter, not the value the interface was declared with.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package a_pkg;
  typedef struct packed {
    int unsigned p_a;
  } cfg_t;
endpackage

interface sub_if #(parameter a_pkg::cfg_t cfg = 0);
  typedef logic [cfg.p_a-1:0] data_t;
  typedef struct packed {
    logic [3:0] addr;
    data_t data;
  } data2_t;
endinterface

module sub (sub_if io);
endmodule

module t();
  parameter a_pkg::cfg_t cfg = '{p_a: 16};

  sub_if #(cfg) sub_io();

  sub u_sub(.io(sub_io));

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
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
