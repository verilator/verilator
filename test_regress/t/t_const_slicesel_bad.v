// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2021 Michael Lefebvre
// SPDX-License-Identifier: CC0-1.0

module t;

  localparam int unsigned A3[2:0] = '{4, 5, 6};

  // slicesel out of range should fail
  localparam int unsigned B32_T[1:0] = A3[3:1];

endmodule
