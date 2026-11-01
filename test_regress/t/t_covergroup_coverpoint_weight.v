// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test procedural coverpoint option.weight access from a constructor.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit a;
  bit b;

  covergroup cg;
    cp1: coverpoint a {
      bins hit = {1};
    }
    cp2: coverpoint b {
      bins hit = {0};
    }
    cx: cross cp1, cp2;
  endgroup

  class coverage_test;
    cg cov;

    function new();
      cov = new();
      cov.cp1.option.weight = 0;
      cov.cx.option.weight = 0;
      `checkd(cov.cp1.option.weight, 0);
      `checkd(cov.cx.option.weight, 0);
      cov.cx.option.weight += 1;
      `checkd(cov.cx.option.weight, 1);
      cov.cx.option.weight = 0;
    endfunction

    function void sample();
      cov.sample();
    endfunction
  endclass

  initial begin
    coverage_test obj;
    obj = new();
    a = 0;
    b = 0;
    obj.sample();
    `checkr(obj.cov.get_inst_coverage(), 100.0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
