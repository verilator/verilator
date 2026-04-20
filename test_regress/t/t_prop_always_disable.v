// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

  bit clk = 0;
  always #5 clk = ~clk;

  logic a = 1'b1;
  logic b = 1'b1;
  logic valid = 1'b1;
  logic rst = 1'b0;
  int   cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 19) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  assert property (@(posedge clk) always [2:5] valid);

  assert property (@(posedge clk) disable iff (rst) always [2:5] valid);

  property p_disable_impl;
    @(posedge clk) disable iff (rst) always [1:2] (a == b);
  endproperty
  assert property (p_disable_impl);

endmodule
