// DESCRIPTION: Verilator: Coverage per-instance hierarchy for inline and no-inline module instances
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module child (
    input clk,
    input en
); /* verilator no_inline_module */
  reg [3:0] count = 0;

  always @(posedge clk) begin
    if (en) begin
      count <= count + 1'b1;
    end else begin
      count <= count;
    end
  end
endmodule

module child_inline (
    input clk,
    input en
); /* verilator inline_module */
  reg [3:0] count = 0;

  always @(posedge clk) begin
    if (en) begin
      count <= count + 1'b1;
    end else begin
      count <= count;
    end
  end
endmodule

module t (
    input clk
);
  reg [3:0] cyc = 0;

  // No-inline current behavior: counters are folded into u_a.
  // True per-instance expected: u_a if=4 else=5, u_b if=1 else=8.
  child u_a (
      .clk(clk),
      .en(cyc < 4)
  );

  child u_b (
      .clk(clk),
      .en(cyc == 0)
  );

  // Inline current behavior: counters are per instance.
  // Expected: i_a if=4 else=5, i_b if=1 else=8.
  child_inline i_a (
      .clk(clk),
      .en(cyc < 4)
  );

  child_inline i_b (
      .clk(clk),
      .en(cyc == 0)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1'b1;
  end
endmodule

module tb;
  reg clk = 0;

  t dut (
      .clk(clk)
  );

  always #1 clk = !clk;

  always @(posedge clk) begin
    if (dut.cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
