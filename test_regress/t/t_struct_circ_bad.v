// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef t1_t;

  typedef struct packed {
    t1_t x;  // <--- Bad: Circular
  } t2_t;

  typedef t2_t [1:0] t3_t;

  typedef t3_t t1_t;  // <--- Bad: Circular (or above)

  t1_t x;

endmodule
