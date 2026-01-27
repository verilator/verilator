// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef int T;

module test (  /*AUTOARG*/
  // Outputs
  bad1, bad2, bad3, bad4
  );
  output [15:0] bad1;
  shortint bad1;  // <--- Error (type doesn't match above)

  output [31:0] bad2;
  T bad2;  // <--- Error (type doesn't match above due to range)

  output [3:0] bad3;
  reg [7:0] bad3;  // <--- Error (range doesn't match) (output-before-reg)

  reg [7:0] bad4;  // <--- Error (range doesn't match) (reg-before-output)
  output [3:0] bad4;

endmodule
