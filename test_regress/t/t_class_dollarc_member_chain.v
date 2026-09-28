// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Inner;
  int x  /*verilator public_flat_rw*/ = 5;
endclass

class Outer;
  Inner m_i  /*verilator public_flat_rw*/ = new;
endclass

module t;
  initial begin
    Outer o;
    o = new;
    `checkd($c(o, "->m_i->x"), 5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
