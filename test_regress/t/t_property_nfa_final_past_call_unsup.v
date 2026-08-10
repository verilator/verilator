// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  bit data;
  bit value;

  default clocking cb @(posedge clk);
  endclocking

  function automatic bit fpast();
    return $past(data);
  endfunction

  function automatic bit fpast_wrapper();
    return fpast();
  endfunction

  task automatic tpast(output bit result);
    result = $past(data);
  endtask

  final begin
    value = $past(data);  // Direct final use remains supported.
    value = fpast_wrapper();
    tpast(value);
  end

endmodule
