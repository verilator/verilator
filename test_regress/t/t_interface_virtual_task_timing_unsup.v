// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

interface clkif (
    input logic clk
);
  int id = 0;
  task automatic wait_any(output int seen_id);
    @(*) seen_id = id;
  endtask
endinterface

module t;
  logic clk = 0;
  always #5 clk = ~clk;
  clkif c (.clk(clk));
  initial begin
    virtual clkif v;
    int s;
    v = c;
    v.wait_any(s);
    $finish;
  end
endmodule
