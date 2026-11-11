// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A C-style '[size]' packed dimension is non-standard (IEEE 1800-2023 7.4.1)

localparam WORDS = 2;
localparam WORD_WIDTH = 64;

class Monitor;
  function int count(logic [WORDS][WORD_WIDTH/8] be);  // <--- Bad (twice)
    int n = 0;
    for (int i = 0; i < WORDS; ++i) begin
      if (be[i] != 0) ++n;
    end
    return n;
  endfunction
endclass

module t;
  typedef logic [7:0] byte_t;

  byte_t [WORDS] bytes;  // <--- Bad
  typedef byte_t [WORDS] bytes_t;  // <--- Bad

  // Unlike a packed dimension, a C-style gate instance array still warns of its ascending range
  wire [WORDS-1:0] gate_in;
  wire [WORDS-1:0] gate_out;
  buf gates[WORDS] (gate_out, gate_in);  // <--- Warning ASCRANGE
endmodule
