// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  logic value  /* verilator forceable */;

  task take_ref(ref logic i);
    // verilator no_inline_task
  endtask

  initial begin
    take_ref(value);
    force value = 1'b1;
    $finish;
  end
endmodule
