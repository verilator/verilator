// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  int loops;

  initial begin
    #1;
    // verilator lint_off INFINITELOOP
    while (1'b1) begin
      $write("*-* All Finished *-*\n");
      $finish;  // Infinite loop, but for this finish
      if (++loops > 100) $stop;
    end
  end

endmodule
