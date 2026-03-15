// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test iff (enable) guard: sampling is gated by the enable condition.
// Samples taken while enable=0 must not increment bins.
// Bins 'disabled_*' are sampled only with enable=0 -- they must NOT appear in
// coverage.dat. Bins 'enabled_*' are sampled only with enable=1 -- they must
// appear. This makes pass/fail unambiguous from the coverage report alone.

module t;
  logic enable;
  int value;

  covergroup cg_iff;
    cp_value: coverpoint value iff (enable) {
      bins disabled_lo = {1};
      bins disabled_hi = {2};
      bins enabled_lo  = {3};
      bins enabled_hi  = {4};
    }
  endgroup

  cg_iff cg = new;

  initial begin
    // Sample disabled_lo and disabled_hi with enable=0 -- must not be recorded
    enable = 0;
    value = 1; cg.sample();
    value = 2; cg.sample();

    // Sample enabled_lo and enabled_hi with enable=1 -- must be recorded
    enable = 1;
    value = 3; cg.sample();
    value = 4; cg.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
