// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Based on ivtest's pr540.v by Steve Williams.
module t;
  bit fail = 0;
  bit abort = 0;

  initial begin
    abort = 1;  // Set here so it's non-constant, otherwise ifs gets folded
    begin : block
      if (abort) disable block;
      fail = 1;  // Don't try to move this in order to merge the 2 ifs
      if (abort) $display("unreachable");
    end
    if (fail) $error("block disable FAILED");
    begin
      // Conditions drawing random values differ, so are not merged
      int a;
      int b;
      int differ;
      repeat (64) begin
        if ($random % 2 != 0) a = 1;
        else a = 2;
        if ($random % 2 != 0) b = 1;
        else b = 2;
        if (a != b) ++differ;
      end
      if (differ == 0) $error("random conditions merged");
    end
    $write("*-* All Finished *-*\n");
    $finish(0);
  end
endmodule
