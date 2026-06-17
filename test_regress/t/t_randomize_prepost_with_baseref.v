// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Base;
  rand bit [7:0] a;
  bit [7:0] m_pre;
  bit [7:0] m_post;
endclass

class Derived extends Base;
  function void pre_randomize;
    `checkd(m_pre, 8'd0);
    m_pre = 8'd10;
  endfunction
  function void post_randomize;
    `checkd(m_pre, 8'd10);
    m_post = a + 8'd1;
  endfunction
endclass

class Base2;
  rand bit [7:0] b;
  bit [7:0] bp;
  bit [7:0] bq;
  function void pre_randomize;
    bp = 8'd1;
  endfunction
  function void post_randomize;
    bq = b;
  endfunction
endclass

class Derived2 extends Base2;
  bit [7:0] dp;
  bit [7:0] dq;
  function void pre_randomize;
    dp = 8'd2;
    super.pre_randomize();
  endfunction
  function void post_randomize;
    dq = b + 8'd1;
    super.post_randomize();
  endfunction
endclass

module t;
  initial begin
    Base b;
    Derived d;
    Base2 b2;
    Derived2 d2;
    int ok;

    // Plain randomize through a base handle already dispatches pre/post
    d = new;
    b = d;
    ok = b.randomize();
    `checkd(ok, 1);
    `checkd(d.m_pre, 8'd10);
    `checkd(d.m_post, d.a + 8'd1);

    // randomize() with through a base handle whose static type lacks pre/post
    d = new;
    b = d;
    ok = b.randomize() with {a == 8'h3c;};
    `checkd(ok, 1);
    `checkd(d.a, 8'h3c);
    `checkd(d.m_pre, 8'd10);
    `checkd(d.m_post, 8'h3d);

    // randomize() with through a base handle that DOES define pre/post,
    // overridden by the derived class with super chaining
    d2 = new;
    b2 = d2;
    ok = b2.randomize() with {b == 8'h11;};
    `checkd(ok, 1);
    `checkd(d2.b, 8'h11);
    `checkd(d2.dp, 8'd2);
    `checkd(d2.bp, 8'd1);
    `checkd(d2.dq, 8'h12);
    `checkd(d2.bq, 8'h11);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
