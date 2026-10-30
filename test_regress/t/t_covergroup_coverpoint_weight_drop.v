// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  class coverage_test;
    bit clk;
    bit value;

    // This event is dropped with --no-timing because clk is not assigned here.
    // verilator lint_off COVERIGN
    covergroup cg @(posedge clk);
      cp: coverpoint value;
    endgroup
    // verilator lint_on COVERIGN

    function new();
      cg = new();
      cg.cp.option.weight = 0;
    endfunction
  endclass

  initial begin
    coverage_test obj;
    obj = new();
    $finish;
  end
endmodule
