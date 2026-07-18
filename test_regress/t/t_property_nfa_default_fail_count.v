// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// A default assertion action fires once per same-tick failing evaluation

module t (
    input clk
);

  int cyc = 0;
  logic [1:0] selector;
  bit nb = 0;
  bit abrt = 0;
  bit zz = 0;

  always_comb begin
    if (cyc == 2) selector = 0;
    else if (cyc == 3) selector = 1;
    else selector = 2;
  end

  assert property (@(posedge clk) case (selector) 0: 1'b1 ##2 1'b0; 1: 1'b1 ##1 1'b0; default: 1'b1;
  endcase);

  assert property (@(posedge clk) not (1'b1 ##[1:2] nb));

  assert property (@(posedge clk) sync_reject_on (abrt) always[0: 1] (!zz));

  always @(posedge clk) begin
    cyc <= cyc + 1;
    nb <= (cyc == 4);
    abrt <= (cyc == 5);
  end

  always @(negedge clk) begin
    if (cyc == 7) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
