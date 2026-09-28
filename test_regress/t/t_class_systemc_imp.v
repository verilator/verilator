// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Other;
`systemc_interface
  static int get();
`systemc_implementation
  int `systemc_class_name::get() { return clsHelper(); }
`verilog
endclass

class Cls;
`systemc_header
inline int clsHelper() { return 42; }
`verilog
endclass

class Holder;
  Cls m_c = new;
endclass

module t;
  initial begin
    Holder h;
    Other o;
    h = new;
    o = new;
    `checkd($c(o, "->get()"), 42);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
