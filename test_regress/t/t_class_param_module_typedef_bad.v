// DESCRIPTION: Verilator: Verilog Test module
//
// Regression test capturing a name-resolution bug:
//   "Reference to 'addr_t' before declaration (IEEE 1800-2023 6.18)"
// when a parameterized module re-typedefs a typedef out of a parameterized
// class via `typedef cls#(...)::name name;`.
//
// Trigger requires: (a) parameterized class with 2+ parameters, and
// (b) the enclosing module itself takes any module parameter. Removing
// either side's parameters makes the error go away, even though the
// SystemVerilog is well-formed and other simulators accept it.
//
// Reduced from pulp-platform/axi tb_axi_iw_converter.sv:182.
//
// Once fixed, this test should be converted into a passing
// `test.compile()` test.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg;
  class rand_master #(parameter int AW = 32, parameter int DW = 32);
    typedef logic [AW-1:0] addr_t;
  endclass
endpackage

module t #(parameter int unused = 1);
  typedef pkg::rand_master #(.AW(32), .DW(64)) rand_master_t;
  typedef rand_master_t::addr_t addr_t;
  initial begin
    static addr_t a = '0;
    $write("a=%h\n", a);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
