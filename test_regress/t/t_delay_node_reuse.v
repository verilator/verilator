// DESCRIPTION: Verilator: Reuse of timed coroutine queue nodes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module t;
  localparam int COUNT = 96;
  localparam int ROUNDS = 4;

  event launch;
  process children[COUNT];
  int order[COUNT];
  bit [COUNT-1:0] seen;
  int round_number;
  int completed;

  for (genvar id = 0; id < COUNT; ++id) begin : g_child
    always @(launch) begin
      children[id] = process::self();
      #1;
      `checkd(seen[id], 0);
      seen[id] = 1;
      if (round_number == 0) order[completed] = id;
      else `checkd(id, order[completed]);
      ++completed;
    end
  end

  initial begin
    #1;
    for (int round_idx = 0; round_idx < ROUNDS; ++round_idx) begin
      round_number = round_idx;
      completed = 0;
      seen = '0;
      ->launch;
      #2;
      `checkd(completed, COUNT);
      `checkd(seen, {COUNT{1'b1}});
    end

    // Leave one full burst suspended while the model is destroyed.
    completed = 0;
    ->launch;
    #0;
    `checkd(completed, 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial #100 `stop;
endmodule
