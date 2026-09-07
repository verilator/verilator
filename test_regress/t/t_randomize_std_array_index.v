// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// A std::randomize() with-clause argument used as an index has no rand
// qualifier of its own, but must still be treated as part of the solve.

module t;
  bit [7:0] probe[2];
  bit [7:0] cube[4][2];
  bit [7:0] p0;
  bit [7:0] q[$];
  int i;
  int ok;

  initial begin
    repeat (30) begin
      ok = std::randomize(probe, cube, i) with { i inside {[0:3]}; probe == cube[i]; };
      if (ok != 1) $stop;
      if (probe != cube[i]) $stop;
    end

    repeat (30) begin
      ok = std::randomize(p0, cube, i) with { i inside {[0:3]}; p0 == cube[i][0]; };
      if (ok != 1) $stop;
      if (p0 != cube[i][0]) $stop;
    end

    repeat (30) begin
      q = {8'h1, 8'h2, 8'h3, 8'h4};
      ok = std::randomize(p0, q, i) with { i inside {[0:3]}; p0 == q[i]; };
      if (ok != 1) $stop;
      if (p0 != q[i]) $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
