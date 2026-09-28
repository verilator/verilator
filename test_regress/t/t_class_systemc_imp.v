// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

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
    if ($c(o, "->get()") != 42) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
