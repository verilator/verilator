// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  reg [2:0] a = 0;

  initial begin
    a = 1;
    if (a != 1) $stop;

    force a = 2;
    if (a != 2) $stop;

    a = 3;
    if (a != 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
