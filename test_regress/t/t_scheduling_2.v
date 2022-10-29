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

  reg clk_half = 0;

  reg [31:0] cyc = 0;
  reg [31:0] a, b, c;

  always @(posedge clk) begin
    $display("tick %d: a: %d, b: %d, c: %d", cyc, a, b, c);
    // Check invariant
    if (a !== cyc + 1) $stop;
    if (b !== cyc + 2) $stop;
    if (c !== cyc + 2) $stop;
    // End of test
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end

    cyc <= cyc + 1;
  end

  always @(clk) a = cyc + `IMPURE_ONE;
  always @(a)   b = a   + `IMPURE_ONE;
  assign        c = a   + `IMPURE_ONE;

endmodule
