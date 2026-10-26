// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef enum logic [6:0] {SMALL = 7'd1} small_t;
  typedef enum logic signed [94:0] {LARGE = -95'sd3} large_t;
  small_t small_value;
  large_t large_value;

  localparam string SMALL_TEXT = $sformatf("%p", small_value);
  localparam string LARGE_TEXT = $sformatf("%p", large_value);

  initial $display("%s:%s", SMALL_TEXT, LARGE_TEXT);
endmodule
