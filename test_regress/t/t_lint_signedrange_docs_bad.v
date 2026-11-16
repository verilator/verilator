// DESCRIPTION: Verilator: Test signed range warning documentation
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [15:0] foo = 65535;  // Warning
  fixed_example ok();
endmodule

module fixed_example;
  logic [15:0] foo = 16'(65535);  // Fixed: explicit size cast
endmodule
