// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Hudson River Trading
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef bit arr_t[3:0];

class C;
  static bit [3:0] last;
  bit [3:0] value;
  function new(bit [3:0] d);
    value = d;
  endfunction
  static function void f(bit [3:0] d);
    last = d;
  endfunction
  static function bit [3:0] g(bit [3:0] d);
    return d;
  endfunction
  function bit [3:0] m(bit [3:0] d);
    return d;
  endfunction
  task t(bit [3:0] d);
    value = d;
  endtask
endclass

module t;
  bit data[3:0];
  arr_t tdata;
  bit q[$];
  C c;
  bit [3:0] mt_value;

  function automatic bit [3:0] mf(bit [3:0] d);
    /*verilator no_inline_task*/
    return d;
  endfunction
  task automatic mt(bit [3:0] d, output bit [3:0] o);
    /*verilator no_inline_task*/
    o = d;
  endtask

  initial begin
    data = '{1'b1, 1'b0, 1'b0, 1'b0};
    tdata = '{1'b0, 1'b1, 1'b1, 1'b0};
    q.push_back(1'b1);
    q.push_back(1'b0);
    q.push_back(1'b1);
    q.push_back(1'b1);

    // Static method
    C::f({>>{data}});
    `checkh(C::last, 4'b1000);
    C::f({<<{data}});
    `checkh(C::last, 4'b0001);
    C::f({<<2{data}});
    `checkh(C::last, 4'b0010);
    C::f({>>{q}});
    `checkh(C::last, 4'b1011);
    C::f({>>{tdata}});
    `checkh(C::last, 4'b0110);
    // Function call within an expression
    `checkh(C::g({>>{data}}), 4'b1000);
    `checkh(C::g({<<{data}}) + 4'd1, 4'b0010);
    // Constructor
    c = new({>>{data}});
    `checkh(c.value, 4'b1000);
    // Non-static method
    `checkh(c.m({<<{data}}), 4'b0001);
    // Class task
    c.t({<<2{data}});
    `checkh(c.value, 4'b0010);
    // Non-inlined module function and task
    `checkh(mf({>>{tdata}}), 4'b0110);
    mt({<<{data}}, mt_value);
    `checkh(mt_value, 4'b0001);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
