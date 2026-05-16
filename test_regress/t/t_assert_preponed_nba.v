// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk = 0;
  int cnt = 0;
  bit fire = 0;

  always #1 clk = ~clk;

  always_ff @(posedge clk) begin
    if (fire) cnt <= cnt + 1;
  end

  assert property (@(posedge clk) fire |-> (cnt == 0))
    $write("Assertion fired and passed: cnt=%0d\n", cnt);
  else begin
    $write("%%Error: sampled fire=1 cnt=%0d, expected preponed cnt 0\n", cnt);
    $stop;
  end

  initial begin
    @(posedge clk);
    fire <= 1;
    @(posedge clk);
    fire <= 0;
    repeat (2) @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
