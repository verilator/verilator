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
  int x /*verilator public_flat_rd*/;
endclass

class Parent1;
  Other m_o /*verilator public_flat_rd*/;
  function new(int xx);
    m_o = new;
    m_o.x = xx;
  endfunction
`systemc_header_post
// global function, uses class's member
inline int otherX(VlClassRef<`systemc_class_name> p) { return p->m_o->x; }
`verilog
endclass

class Parent2;
  Other m_o /*verilator public_flat_rd*/;
  function new(int xx);
    m_o = new;
    m_o.x = xx;
  endfunction
`systemc_interface
// member function, uses class's member
inline int otherX() { return m_o->x; }
`verilog
endclass

class Parent3;
  Other m_o /*verilator public_flat_rd*/;
  function new(int xx);
    m_o = new;
    m_o.x = xx;
  endfunction
`systemc_header
// global function before class, uses class's member
class `systemc_class_name;
template <typename T> int otherX(const VlClassRef<T>& p) { return p->m_o->x; }
`verilog
endclass

module t;
  initial begin
    Parent1 p1;
    Parent2 p2;
    Parent3 p3;
    p1 = new(7);
    p2 = new(17);
    p3 = new(29);
    `checkd($c("otherX(",p1,")"), 7);
    `checkd($c(p2,"->otherX()"), 17);
    `checkd($c("otherX(",p3,")"), 29);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
