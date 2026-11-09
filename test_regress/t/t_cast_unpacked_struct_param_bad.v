// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A bit-stream cast of a non-constant parameter value. Not in t_cast_unpacked_struct_bad.v, as an
// error in a parameter value ends the elaboration before other errors.

module t;

  typedef struct {
    byte hi;
    byte lo;
  } s16_t;

  int calls = 0;

  function automatic shortint next();
    calls++;
    return 16'(calls);
  endfunction

  localparam s16_t P = s16_t'(next());  // Bad: not a constant

  initial $display("%h", P.hi);

endmodule
