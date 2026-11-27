// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk = 0;
  initial forever #1 clk = ~clk;

  localparam MAX = 3;
  integer cyc = 1;
  int a = 0, b = 3;

  assert property (@(posedge clk) eventually[0: b] 1'b0);
  assert property (@(posedge clk) eventually[a: 3] 1'b0);
  assert property (@(posedge clk) eventually[a: b] 1'b0);
  assert property (@(posedge clk) eventually[0: $] 1'b0);
  assert property (@(posedge clk) eventually[-1: 5] 1'b0);
  assert property (@(posedge clk) eventually[-2: -3] 1'b0);
  assert property (@(posedge clk) eventually[5: 0] 1'b0);
  assert property (@(posedge clk) eventually[0: -1] 1'b0);

  localparam string LO = "";
  typedef string bound_t;
  localparam bound_t HI = "";
  assert property (@(posedge clk) eventually[LO: 1] 1'b0);
  assert property (@(posedge clk) eventually[0: HI] 1'b0);
  assert property (@(posedge clk) eventually[0.0: 1] 1'b0);
  assert property (@(posedge clk) eventually[0: 1.0] 1'b0);

  assert property (@(posedge clk) s_eventually[$: 2] 1'b0);
  assert property (@(posedge clk) s_eventually[-1: $] 1'b0);
  assert property (@(posedge clk) s_eventually[0: -1] 1'b0);
  assert property (@(posedge clk) s_eventually[0.5: $] 1'b0);
  assert property (@(posedge clk) s_eventually[0: HI] 1'b0);
  assert property (@(posedge clk) a |-> s_eventually[0:65537] b);

  always @(posedge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
