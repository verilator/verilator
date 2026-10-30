// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef class Derived;

class Base;
  Derived m_d /*verilator public_flat_rd*/;
`systemc_interface
  int get();
`systemc_implementation
  int `systemc_class_name::get() { return m_d->dummy; }
`verilog
endclass

class Derived extends Base;
  int dummy /*verilator public_flat_rd*/;
endclass

module t;
  initial begin
    Base b;
    b = new;
    b.m_d = new;
    b.m_d.dummy = 1;
    `checkd($c(b,"->get()"),1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
