// DESCRIPTION: Verilator: Test of UNSYNTHESIZABLE warning on / % ** operators
//
// SPDX-FileCopyrightText: 2026 Lucas Amaral
// SPDX-License-Identifier: CC0-1.0

module t (input wire [7:0] a, b, output wire [7:0] q);
  assign q = a / b;
endmodule
