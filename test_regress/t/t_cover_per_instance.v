// DESCRIPTION: Verilator: Coverage per-instance hierarchy for duplicate module instances
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module child (
    input clk,
    input en
);
`ifdef INLINE_CHILD  //verilator inline_module
`else  //verilator no_inline_module
`endif
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

  // Over 9 clock edges, u_a.en is true for cyc 0..3, so u_a should report
  // if coverage of 4, else coverage of 5, and line coverage of 9.
  child u_a (
      .clk(clk),
      .en(cyc < 4)
  );

  // u_b.en is true only for cyc 0, so u_b should report if coverage of 1,
  // else coverage of 8, and line coverage of 9.
  child u_b (
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
