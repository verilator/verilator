// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`ifdef VERILATOR
// The '$c1(1)' is there to prevent inlining of the signal by V3Gate
`define IMPURE_ONE $c(1)
`else
// Use standard $random (chaces of getting 2 consecutive zeroes is zero).
`define IMPURE_ONE |($random | $random)
`endif

module t;
  initial begin
    $write("%f\n", `IMPURE_ONE ? 1.234 : 1.234);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
