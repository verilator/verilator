// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Based on icarus/ivtest/ivltests/sv_class_super6.v

class B;
  int m_x, m_y;

  task set_y;
    m_y = 2000;
  endtask

  function void check_x;
    `checkd(m_x, 1000);
  endfunction
endclass

class C extends B;
  byte m_x, m_y;
  task set_x;
    m_x = 6;
    this.m_y = 7;
    this.super.m_x = 1000;
  endtask

  function void check_y;
    `checkd(m_x, 6);
    `checkd(this.m_y, 7);
    `checkd(this.super.m_y, 2000);
  endfunction
endclass

module test;
  C c;

  initial begin
    c = new;
    c.set_x();
    c.set_y();
    c.check_x();
    c.check_y();
    $finish;
  end
endmodule
