// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test: a transition sequence longer than supported

// verilog_format: off
// A sequence of 2^N alternating values 0, 1, 0, ...
`define SEQ2 0 => 1
`define SEQ4 `SEQ2 => `SEQ2
`define SEQ8 `SEQ4 => `SEQ4
`define SEQ16 `SEQ8 => `SEQ8
`define SEQ32 `SEQ16 => `SEQ16
`define SEQ64 `SEQ32 => `SEQ32
`define SEQ128 `SEQ64 => `SEQ64
`define SEQ256 `SEQ128 => `SEQ128
// verilog_format: on

module t;
  bit v;

  covergroup cg;
    cp: coverpoint v {
      bins seq = (`SEQ256 => 0);  // 257 values
    }
  endgroup

  cg cg_inst = new;
endmodule
