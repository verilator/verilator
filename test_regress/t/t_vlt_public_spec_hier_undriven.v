// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


module sub();
  logic [7:0] orphan;
endmodule

module top();
  sub sub_a ();
  sub sub_b ();
endmodule
