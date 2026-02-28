// -*- Verilog -*-
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test requires command line be passed uvm_pkg.sv before this filename

// verilator lint_off DECLFILENAME

module t;
  import uvm_pkg::*;
  // verilator lint_off UNUSEDSIGNAL
  // verilator lint_off WIDTHTRUNC
  class test extends uvm_test;

    `uvm_component_utils(test)

    function new(string name, uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      $write("** UVM TEST PASSED **\n");
    endfunction
  endclass

  initial begin
    run_test("test");
  end
endmodule
