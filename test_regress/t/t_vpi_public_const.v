// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Will Keen
// SPDX-License-Identifier: CC0-1.0

module t;
  wire v /*verilator public_flat_rw*/ = 1'b1;
  wire r /*verilator public_flat_rd*/ = v;
endmodule
