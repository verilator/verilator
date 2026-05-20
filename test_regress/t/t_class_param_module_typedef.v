// DESCRIPTION: Verilator: Verilog Test module
//
// Regression test for a name-resolution bug:
// A parameterized module that re-typedefs a typedef out of a parameterized
// class (`typedef cls#(...)::name name;`) used to spuriously fail with
// "Reference to '<name>' before declaration (IEEE 1800-2023 6.18)" when
// the parameterized class had 2+ parameters and the enclosing module had
// any module parameter. Reduced from pulp-platform/axi
// tb_axi_iw_converter.sv:182.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package pkg;
  class rand_master #(
      parameter int AW = 32,
      parameter int DW = 32
  );
    typedef logic [AW-1:0] addr_t;
  endclass
endpackage

module t #(
    parameter int unused = 1
);
  // AW and DW are both overridden to non-default values so that a regression
  // in parameter propagation through the typedef chain shows up as a width
  // mismatch instead of silently succeeding.
  typedef pkg::rand_master#(
      .AW(17),
      .DW(64)
  ) rand_master_t;
  typedef rand_master_t::addr_t addr_t;
  initial begin
    static addr_t a = '0;
    `checkd($bits(addr_t), 17);
    `checkd($bits(a), 17);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
