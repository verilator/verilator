// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Zhi QU
// SPDX-License-Identifier: CC0-1.0

module t (
    input  logic [3:0] v,
    output logic [6:0] y
);

  assign y[0] = !|v;
  assign y[1] = !&v;
  assign y[2] = !^v;
  assign y[3] = !~^v;
  assign y[4] = !^~v;
  assign y[5] = !~&v;
  assign y[6] = !~|v;

endmodule
