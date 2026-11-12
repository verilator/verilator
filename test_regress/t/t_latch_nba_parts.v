// DESCRIPTION: Verilator: Sensitivity of an always_latch with nonblocking assignments
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;
  always @(posedge clk) cyc <= cyc + 1;

  // A flop stage and a latch stage, transparent while clk is high, in one vector and in one
  // array. The latch follows the flop output that changes just after it opens.
  logic [7:0] stage = 0;
  always @(posedge clk) stage[3:0] <= stage[3:0] + 4'd3;
  always_latch if (clk) stage[7:4] <= stage[3:0];

  logic [3:0] stages[2];
  initial begin
    stages[0] = 0;
    stages[1] = 0;
  end
  always @(posedge clk) stages[0] <= stages[0] + 4'd5;
  always_latch if (clk) stages[1] <= stages[0];

  // Packed fields inside each unpacked word are independent sensitivity sources.
  logic [7:0] word_stages[2];
  initial begin
    word_stages[0] = 0;
    word_stages[1] = 0;
  end
  always @(posedge clk) begin
    word_stages[0][3:0] <= word_stages[0][3:0] + 4'd3;
    word_stages[1][3:0] <= word_stages[1][3:0] + 4'd5;
  end
  always_latch if (clk) begin
    word_stages[0][7:4] <= word_stages[0][3:0];
    word_stages[1][7:4] <= word_stages[1][3:0];
  end

  // Flops on the edge that opens the latches see their previous outputs
  logic [3:0] q, qs;
  always @(posedge clk) q <= stage[7:4];
  always @(posedge clk) qs <= stages[1];

  // A function that is not inlined: its argument is not a sensitivity
  function automatic logic [3:0] transform(input logic [3:0] x);
    // verilator no_inline_task
    return x ^ 4'h5;
  endfunction
  logic [3:0] tq;
  always_latch if (clk) tq <= transform(stage[3:0]);

  logic [3:0] lo_q = 0, lo_qs = 0;
  always @(negedge clk) begin
    if (cyc > 1) begin
      `checkh(stage[7:4], stage[3:0]);
      `checkh(stages[1], stages[0]);
      `checkh(word_stages[0][7:4], word_stages[0][3:0]);
      `checkh(word_stages[1][7:4], word_stages[1][3:0]);
      `checkh(tq, stage[3:0] ^ 4'h5);
      `checkh(q, lo_q);
      `checkh(qs, lo_qs);
    end
    lo_q = stage[3:0];
    lo_qs = stages[0];
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
