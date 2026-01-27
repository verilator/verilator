// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Geza Lore
// SPDX-License-Identifier: CC0-1.0

module t;
  wire a;
  wire b;
  wire c;
  assign a = b;
  assign b = c;
  assign c = a;
endmodule
