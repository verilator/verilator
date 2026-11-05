// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input int a,
    input int b,
    output int x,
    output int y
);
  // The closures of the two NBAs to 'x' have the same function, so it is combined. That of the NBA
  // to 'y' updates another variable, so it is not.
  initial begin
    x <= a;
    x <= b;
    y <= a;
  end
endmodule
