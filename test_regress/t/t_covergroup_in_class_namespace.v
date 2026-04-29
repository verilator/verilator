// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class myClass;
  covergroup embeddedCg;
    cp_mc: coverpoint 1'b1;
  endgroup

  function new();
    real cov_result;
    embeddedCg = new();
    embeddedCg.sample();
    cov_result = embeddedCg.get_coverage();
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_coverage() out of range: %f", cov_result);
  endfunction
endclass

class secondClass;
  covergroup embeddedCg;
    cp_sc: coverpoint 1'b0;
  endgroup

  function new();
    real cov_result;
    embeddedCg = new();
    embeddedCg.sample();
    cov_result = embeddedCg.get_coverage();
    if (!(cov_result >= 0.0 && cov_result <= 100.0))
      $error("%m: get_coverage() out of range: %f", cov_result);
  endfunction
endclass

// verilator lint_off COVERIGN
module t;
  myClass mc;
  secondClass sc;
  initial begin
    mc = new();
    sc = new();
    $finish;
  end
endmodule
// verilator lint_on COVERIGN
