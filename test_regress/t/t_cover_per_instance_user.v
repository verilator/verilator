// DESCRIPTION: Verilator: User coverage per-instance records for the same statement
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module child (
    input clk,
    input en
);
  reg observed = 1'b0;
  reg [3:0] count = 0;

  same_stmt:
    cover property (@(posedge clk) en);

  always @(posedge clk) begin
    observed <= en;
    if (en) begin
      count <= count + 1'b1;
    end else begin
      count <= count;
    end
  end
endmodule

module wrap (
    input clk,
    input en
);
  child dut_b (
      .clk(clk),
      .en(en)
  );
endmodule

module tb;
  reg clk = 0;
  reg [3:0] cyc = 0;

  // Same user cover statement at two different hierarchy points.
  // Expected with per_instance: dut_a count=4, wrap_b.dut_b count=1.
  child dut_a (
      .clk(clk),
      .en(cyc < 4)
  );

  wrap wrap_b (
      .clk(clk),
      .en(cyc == 0)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1'b1;
  end

  always #1 clk = !clk;

  always @(posedge clk) begin
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
