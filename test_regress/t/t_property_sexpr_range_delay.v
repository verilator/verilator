// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;

  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // --- Test 1: basic ##[1:3] with trivially-true expression ---
  event e1;
  always @(negedge clk) if (cyc >= 1 && cyc <= 20) ->e1;

  a1: assert property (@(e1) ##[1:3] 1);

  // --- Test 2: ##[2:4] with trivially-true expression ---
  event e2;
  always @(negedge clk) if (cyc >= 30 && cyc <= 50) ->e2;

  a2: assert property (@(e2) ##[2:4] 1);

  // --- Test 3: degenerate ##[2:2] (equivalent to ##2) ---
  event e3;
  always @(negedge clk) if (cyc >= 60 && cyc <= 80) ->e3;

  a3: assert property (@(e3) ##[2:2] 1);

  // --- Test 4: multi-step ##[1:2] b ##1 c (both b and c always true) ---
  event e4;
  always @(negedge clk) if (cyc >= 1 && cyc <= 20) ->e4;

  a4: assert property (@(e4) ##[1:2] 1 ##1 1);

endmodule
