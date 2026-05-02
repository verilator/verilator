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
    embeddedCg = new();
    embeddedCg.sample();
    void'(embeddedCg.get_coverage());
  endfunction
endclass

class secondClass;
  covergroup embeddedCg;
    cp_sc: coverpoint 1'b0;
  endgroup

  function new();
    embeddedCg = new();
    embeddedCg.sample();
    void'(embeddedCg.get_coverage());
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
