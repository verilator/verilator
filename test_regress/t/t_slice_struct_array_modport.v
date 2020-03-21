// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Varun Koyyalagunta.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
  logic  p;
} s_data;

module m1 (output s_data data[1:0]);
  assign data[0].p = 0;
  assign data[1].p = 0;
endmodule

module top (output s_data data[2:0]);
  m1 m1_inst (.data(data[1:0]));
endmodule
