// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  class Cls;
    task test_srandom;
      int i, j, k;
      // $urandom is per-process thread, not affected by object stability/this.srandom(seed)
      // "Each object maintains its own internal RNG, which is used exclusively by its randomize() method."
      // THis was moved to t_rand_stability_class.v
      this.srandom(1234);
      i = $urandom;
      this.srandom(1234);
      j = $urandom;
      this.srandom(1234);
      k = $urandom;
      if (i == j && i == k) $stop;  // Small chance randomly i == j, or j == k
    endtask
  endclass

  Cls c1;

  initial begin
    c1 = new;
    c1.test_srandom;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
