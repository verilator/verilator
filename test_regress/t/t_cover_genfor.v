// DESCRIPTION: Verilator: Coverage per generate-for iteration (issue #9036)
//
// Verifying that --coverage-per-instance distinguishes branch and expression
// coverage points across unrolled generate-for iterations.  Each iteration is
// a separate begin-name, so its coverage points carry a unique hierarchy.
// Before the fix all iterations shared one hierarchy and merged into a single
// point, which made per-iteration analysis impossible without wrapping the
// logic in a duplicated sub-module.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module tb;
  reg clk = 0;
  reg [7:0] a = 0;
  reg [7:0] b = 0;

  always #1 clk = !clk;

  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : g_loop
      always @(posedge clk) begin
        if (a[i] == 0) begin
          a[i] <= 1;
        end
        else begin
          a[i] <= 0;
        end
        b[i] <= !a[i];
      end
    end
  endgenerate

  initial begin
    a = 8'b10101010;
    repeat (4) @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
