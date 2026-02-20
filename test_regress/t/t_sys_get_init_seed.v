// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Srinivasan Venkataramanan
// SPDX-License-Identifier: CC0-1.0

module t;
  int seed = 1;

  initial begin
    seed = $get_initial_random_seed();
    $display("get_initial_random_seed=%0d", seed);
    if (seed != 22) $stop;
    $write("*-* All Finished *-*\n");
    $finish(2);
  end

endmodule
