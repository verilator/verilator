// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  int seed;
  initial begin
    seed = $get_initial_random_seed();
    $display("seed=%0d", seed);
    if (seed == 0) $stop;  // +verilator+seed+0 must be replaced by a non-zero picked seed
    $write("*-* All Finished *-*\n");
    $finish(2);
  end
endmodule
