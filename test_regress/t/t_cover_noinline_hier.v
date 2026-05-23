// DESCRIPTION: Verilator: Hierarchical user coverage in no-inline module instances
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module child (
    input clk,
    input en,
    output reg seen
); /* verilator no_inline_module */
  // The user cover and generated line/branch coverage below share one
  // no-inline module body but must produce independent counters per instance.
  same_stmt:
    cover property (@(posedge clk) en);

  always @(posedge clk) begin
    if (en) seen <= 1'b1;
  end
endmodule

module t (
    input clk
);
  reg [3:0] cyc = 0;
  wire seen_a;
  wire seen_b;

  // Over 9 clock edges, u_a.en is true for cyc 0..3, so u_a should report
  // user/if coverage of 4, else coverage of 5, and line coverage of 9.
  child u_a (
      .clk(clk),
      .en(cyc < 4),
      .seen(seen_a)
  );

  // u_b.en is true only for cyc 0, so u_b should report user/if coverage of
  // 1, else coverage of 8, and line coverage of 9. These different counts
  // prove the duplicate no-inline child instances did not collapse together.
  child u_b (
      .clk(clk),
      .en(cyc == 0),
      .seen(seen_b)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1'b1;
  end
endmodule
