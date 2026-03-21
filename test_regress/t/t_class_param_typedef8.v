// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test for issue #5977: Typedef of parameterized class for member access

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  class cls_l0 #(parameter AW = 32);
    logic [AW-1:0] addr;
    function new();
      addr = '0;
    endfunction
  endclass

  class cls_l1 #(parameter int AW = 32);
    typedef cls_l0 #(.AW(AW)) beat_t;
  endclass
endpackage

module t;
  // Typedef of parameterized class, then access member typedef via ::
  typedef pkg::cls_l1 #(.AW(64)) drv64_t;
  typedef pkg::cls_l1 #(.AW(128)) drv128_t;

  initial begin
    // Access class-type typedef member through module-level typedef
    automatic drv64_t::beat_t item1 = new;
    automatic drv128_t::beat_t item2 = new;
    item1.addr = 64'hDEAD_BEEF_CAFE_BABE;

    `checkd(item1.addr, 64'hDEAD_BEEF_CAFE_BABE);
    `checkd($bits(item1.addr), 64);
    `checkd($bits(item2.addr), 128);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
