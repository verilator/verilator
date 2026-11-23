// DESCRIPTION: Verilator: Coverage per generate-for iteration (issue #9036)
//
// Verifying that --coverage-per-instance distinguishes line, branch and
// expression points across unrolled generate-for iterations.  Each iteration
// is a separate begin-name, so its points carry a unique hierarchy; the same
// design without --coverage-per-instance keeps the module-only hierarchy, so
// the default report is unchanged.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module tb;
  reg clk = 0;
  reg [7:0] a = 0;
  reg [7:0] b = 0;
  reg [7:0] c = 0;
  reg [7:0] d = 0;

  always #1 clk = !clk;

  genvar i;

  // Labeled generate-for (the reported case)
  generate
    for (i = 0; i < 4; i++) begin : g_loop
      always @(posedge clk) begin
        if (a[i] == 0) a[i] <= 1;
        else a[i] <= 0;
        b[i] <= !a[i];
      end
    end
  endgenerate

  // Unlabeled generate-for
  generate
    for (i = 0; i < 4; i++) begin
      always @(posedge clk) begin
        if (c[i] == 0) c[i] <= 1;
        else c[i] <= 0;
      end
    end
  endgenerate

  // Generate-for with a named begin nested inside each iteration
  generate
    for (i = 0; i < 4; i++) begin : g_nest
      always @(posedge clk) begin : g_body
        if (d[i] == 0) d[i] <= 1;
        else d[i] <= 0;
      end
    end
  endgenerate

  initial begin
    a = 8'b10101010;
    c = 8'b10101010;
    d = 8'b10101010;
    repeat (4) @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  // A loop declaring its variable, an unnamed block, inside each iteration
  reg [3:0] e = 0;
  generate
    for (i = 0; i < 2; i++) begin : g_decl
      always @(posedge clk) begin
        for (int j = 0; j < 2; j++) begin
          if (e[i*2+j] == 0) e[i*2+j] <= 1;
        end
      end
    end
  endgenerate

  // A named procedural block with an unnamed loop block inside, and user covers
  reg [3:0] f = 0;
  always @(posedge clk) begin : b_named
    for (int j = 0; j < 2; j++) begin
      if (f[j] == 0) f[j] <= 1;
      cover (f[j]);
    end
    for (int k = 0; k < 2; k++) cover (f[k]);
  end
  generate
    for (i = 0; i < 2; i++) begin : g_cover
      cover property (@(posedge clk) f[i]);
    end
  endgenerate
endmodule
