// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2022 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef VERILATOR
// The '$c1(1)' is there to prevent inlining of the signal by V3Gate
`define IMPURE_ONE $c(1);
`else
// Use standard $random (chaces of getting 2 consecutive zeroes is zero).
`define IMPURE_ONE |($random | $random);
`endif

module top(
  clk
);

  input clk;

  // Generate half speed 'clk_half', via non-blocking assignment
  reg clk_half = 0;
  always @(posedge clk)
    clk_half <= ~clk_half;

  // 'clk_half_also' is the same as 'clk_half'.
  wire clk_half_also = clk_half & `IMPURE_ONE;

  // Random data updated by full speed clock
  reg q = 0;
  always @(posedge clk)
    q <= ($random % 2 == 1) ? 1'b1 : 1'b0;

  // Flop `q` via `clk_half`
  reg a = 0;
  always @(posedge clk_half)
    a <= q;

  // Flop `q` via `clk_half_also`
  reg b = 0;
  always @(posedge clk_half_also)
    b <= q;

  // Cycle count
  reg [31:0] cyc = 0;

  // `a` should always equal `b`, no mater which value they actually capture
  always @(posedge clk) begin
    if (a !== b) begin
      $display("tick %d: a is %1d, b is %1d (q is %1d)", cyc, a, b, q);
      $stop;
    end
  end

  // Just stop condition
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
