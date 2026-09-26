// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  task scalar_arg(int value);
  endtask

  initial begin
    int i;

    i = {} + 1;

    i = {};

    scalar_arg({});

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
