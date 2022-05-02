// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2022 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

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
    if (cyc + 1 !== a) $stop;
    if (cyc + 2 !== b) $stop;
    if (cyc + 2 !== c) $stop;
    // End of test
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end

    cyc <= cyc + 1;
  end

  always @(posedge clk) a = cyc + $c(1);
  always @(a)   b = a + $c(1);
  assign        c = a + $c(1);

endmodule
