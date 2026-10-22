// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  int a[3];

  initial begin
    for (int i = 0; i < 2; i++) begin
      fork
        break;  // Illegal 12.8
      join
    end
    repeat (2) begin
      fork
        begin
          continue;  // Illegal 12.8
        end
      join_none
    end
    foreach (a[i]) begin
      fork
        for (int j = 0; j < 2; j++) begin
          if (j == 1) break;  // OK, loop inside fork
          fork
            continue;  // Illegal 12.8
          join_any
        end
      join
    end
  end
endmodule
