// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    repeat (1000000) begin
      fork
        begin
          automatic process p = process::self();
          #1;
        end
      join
    end
    $finish;
  end
endmodule
