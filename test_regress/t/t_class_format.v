// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2021 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
  bit b;
  int i;
  bit [15:0] carray4[4];
  bit [64:0] cwide[2];
  string name;
  real r;
  task debug();
    $display("DEBUG: %s (@%0t) %s", this.name, $realtime, "message");
  endtask
endclass

class Base;
  int m_in_base;
endclass

class ClsA extends Base;
  int m_in_a;
  Base m_b;
endclass

class ClsB extends Base;
  int m_in_b;
  Base m_a;
endclass

module t;
  initial begin
    Cls c;
    ClsA ca;
    ClsB cb;

    c = new;
    c.b = '1;
    c.i = 42;
    c.r = 2.2;
    c.name = "object_name";

    c.carray4[0] = 16'h11;
    c.carray4[1] = 16'h22;
    c.carray4[2] = 16'h33;
    c.carray4[3] = 16'h44;
    $display("'%p'", c);

    c.carray4 = '{16'h911, 16'h922, 16'h933, 16'h944};
    $display("'%p'", c);

    c.debug();

    ca = new;
    $display("'%p'", ca);
    cb = new;
    ca.m_b = cb;
    $display("'%p'", ca);
    cb.m_a = ca;  // Circular
    $display("'%p'", ca);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
