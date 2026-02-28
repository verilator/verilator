// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input [3:1] i3,
    input [4:1] i4,
    output [3:1] o3,
    output [4:1] o4
);

  // verilator lint_off WIDTHTRUNC,WIDTHEXPAND  // after slashes ignored
  assign o3 = i4;
  assign o4 = i3;

endmodule
