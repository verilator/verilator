// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Leaf;
  int x /*verilator public_flat_rw*/;
endclass

class Mid;
  Leaf m_leaf /*verilator public_flat_rd*/ = new;
endclass

class Holder;
  Mid m_mid /*verilator public_flat_rd*/ = new;
`systemc_ctor
  m_mid->m_leaf->x = 42;
`systemc_dtor
  m_mid->m_leaf->x = 0;
`verilog
endclass

module t;
  initial begin
    Holder h;
    h = new;
    `checkd(h.m_mid.m_leaf.x, 42);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
