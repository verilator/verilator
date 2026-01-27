// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  wire array1[2:1];
  wire [2:-1] vec;

  integer bad_index = 1;

  parameter P_ONE = 1;

  initial begin
    force array1[P_ONE] = 1'b1;  // ok
    release array1[P_ONE];  // ok
    force vec[P_ONE+:1] = 1'b1;  // ok
    release vec[P_ONE+:1];  // ok

    // IEEE 1800-2023 10.6.2 [A force] shall not be a bit-select or a
    // part-select of a [non-constant] variable or of a net with a user-defined
    // nettype.
    force array1[bad_index] = 1'b1;  // <---- BAD not constant index
    release array1[bad_index];  // <---- BAD not constant index
    force vec[bad_index+:1] = 1'b1;  // <---- BAD not constant index
    release vec[bad_index+:1];  // <---- BAD not constant index
  end

endmodule
