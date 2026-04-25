// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int x1;
  initial begin
    t1(x1);
    $finish;
  end
  task t1(ref int x);
    fork
      x = #1 2;
    join_none
  endtask
endmodule
