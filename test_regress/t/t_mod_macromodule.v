// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

macromodule t;
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
