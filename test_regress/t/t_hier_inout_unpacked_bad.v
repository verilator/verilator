// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  wire x [3];
  sub dut (.x(x));
endmodule

module sub (inout wire x [3]);
  /* verilator hier_block */
  // Lowering this receive-only inout creates assignments that V3Slice rejects.
endmodule
