// -*- Verilog -*-
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test requires command line be passed uvm_pkg.sv before this filename

// verilator lint_off DECLFILENAME

module t;
  import uvm_pkg::*;
  initial begin
    // verilator lint_off WIDTHTRUNC
    `uvm_info("TOP", "UVM TEST PASSED", UVM_MEDIUM);
  end
endmodule
