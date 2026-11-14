// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  initial begin
    // Uses the std package, which gets no coverage points
    automatic process p = process::self();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
