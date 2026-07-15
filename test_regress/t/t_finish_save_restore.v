// DESCRIPTION: Verilator: Save and restore $finish propagation state
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

module t (
    input  logic trigger,
    output logic after
);
  always_comb begin
    after = 1'b0;
    if (trigger) begin
      $finish;
      after = 1'b1;
    end
  end
endmodule
