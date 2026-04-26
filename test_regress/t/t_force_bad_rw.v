// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  int value;

  task increment(ref int i);
    // verilator no_inline_task
    ++i;
  endtask

  initial begin
    value = 3;
    increment(value);

    force value = 0;
    $display("ii %d\n", value);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
