// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test that two currently-unsupported coverpoint reference styles are properly flagged
// as COVIGN: references to containing-class members ; references to covergroup formal
// parameters

class ubus_transfer;
  bit [15:0] addr;
  bit read_write;
endclass

class ubus_master_monitor;
  ubus_transfer trans_collected;

  // Coverpoints reference 'trans_collected', a member of the enclosing class.
  // A cross is included so the safety-net cleanup also exercises cross removal.
  covergroup cov_trans;
    trans_start_addr: coverpoint trans_collected.addr {option.auto_bin_max = 16;}
    trans_dir: coverpoint trans_collected.read_write;
    trans_addr_x_dir : cross trans_start_addr, trans_dir;
  endgroup

  function new();
    trans_collected = new;
    cov_trans = new;
  endfunction
endclass

class coverage_state;
  bit [3:0] test;
  bit [3:0] test2;
endclass

class parameterized_monitor;
  coverage_state cs;

  // Parameterized covergroup: the coverpoints dereference the class-handle argument 'st'.
  // Two handle-dereferencing coverpoints ensure the safety net reports only the first
  // offender (a second AstMemberSel is seen with the offender already latched).
  covergroup cov_param(coverage_state st);
    cp: coverpoint st.test;
    cp2: coverpoint st.test2;
  endgroup

  function new();
    cs = new;
    cov_param = new(cs);
  endfunction
endclass

module t;
  ubus_master_monitor m;
  parameterized_monitor p;
  initial begin
    m = new;
    p = new;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
