// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  bit data;

  function automatic bit fpast_explicit_clock();
    return $past(data, 1, 1'b1, @(posedge clk));
  endfunction

  final begin
    // Explicit-clock $past is rejected globally before final-call lowering.
    data = fpast_explicit_clock();
  end

endmodule
