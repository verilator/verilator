// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic clk_a = 0;
  always #3 clk_a = ~clk_a;

  int drive_a = 0;
  int seen_a = 0;
  int drive_a_pending = 0;
  int react_a_count = 0;

  default clocking cb_a @(posedge clk_a);
    input #0 drive_a;
    output #0 drive_a_pending;
  endclocking

  // Many independent clocks so the trigger vector needs a second word
  wire [69:0] alive;
  for (genvar i = 0; i < 70; ++i) begin : g
    logic clk = 0;
    int count = 0;
    always #(2 + i) clk = ~clk;
    always @(posedge clk) count <= count + 1;
    assign alive[i] = count != 0;
  end

  logic clk_b = 0;
  always #5 clk_b = ~clk_b;

  int drive_b = 0;
  int seen_b = 0;
  int drive_b_pending = 0;

  clocking cb_b @(posedge clk_b);
    input #0 drive_b;
    output #0 drive_b_pending;
  endclocking

  always @(posedge clk_a) drive_a <= drive_a + 3;
  always @(posedge clk_b) drive_b <= drive_b + 5;

  // The #0 input skew samples in Observed: the NBA of the same edge is visible
  always @(posedge clk_a) seen_a <= cb_a.drive_a;
  always @(posedge clk_b) seen_b <= cb_b.drive_b;

  initial begin
    repeat (4) @(posedge clk_a);
    cb_a.drive_a_pending <= 21;
    repeat (3) @(posedge clk_b);
    cb_b.drive_b_pending <= 35;
    @(posedge clk_b);
    #101;
    `checkd(seen_a, 75);
    `checkd(drive_a, 78);
    `checkd(seen_b, 75);
    `checkd(drive_b, 80);
    `checkd(drive_a_pending, 21);
    `checkd(drive_b_pending, 35);
    `checkd(g[0].count, 39);
    `checkd(g[69].count, 1);
    `checkd(alive, {70{1'b1}});
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
