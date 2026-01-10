// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module randcase_tb;
  int count;
  initial begin
    for (int i = 0; i < 100; i++) begin
      fork
        randcase
          1: count++;
          5: count--;
          3: ;
        endcase
      join_none
    end
    #1;
    if (count > 30) $stop;  // Realistically won't happen (10^25) though not impossible
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
