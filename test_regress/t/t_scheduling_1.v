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

  // Generate half speed 'clk_half', via blocking assignment
  reg clk_half = 0;
  always @(posedge clk)
    clk_half = ~clk_half;

  // Cycle count (+ stop condition)
  reg [31:0] cyc = 0;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Flop cycle count via `clk`
  reg [31:0] a = 0;
  always @(posedge clk)
    a <= cyc;

  // Flop cycle count via `clk_half`, on both edges
  reg [31:0] b = 0;
  always @(posedge clk_half or negedge clk_half)
    b <= cyc;

  // `a` should always equal `b`, no mater which value they actually capture
  always @(posedge clk) begin
    if (a !== b) begin
      $display("tick %d: a is %x, b is %x", cyc, a, b);
      $stop;
    end
  end
endmodule
