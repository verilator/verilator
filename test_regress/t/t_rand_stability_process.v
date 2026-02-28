// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Aleksander Kiryk
// SPDX-License-Identifier: CC0-1.0

// This test checks if calls to get_randstate don't affect
// the state of RNG.

module t;
  integer a1, a2, b1, b2;
  string s1, s2;
  process p;

  initial begin
    p = process::self();

    // 1. Take two random values with get_randstate call in between
    s1 = p.get_randstate();
    a1 = $urandom;
    s2 = p.get_randstate();
    a2 = $urandom;

    // 2. Take two random values again, this time without the call
    p.set_randstate(s1);
    b1 = $urandom;
    b2 = $urandom;

    // The initial state of RNG was restored before step 2., so each
    // corresponding call to $urandom should return the same value.
    if (a1 != b1) $stop;
    if (a2 != b2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
