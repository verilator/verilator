// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

typedef class Foo;

virtual class Bar #(type T);
  T m_val;
endclass

class Baz;
  rand bit [3:0] m_sus;
endclass

class Foo extends Bar#(Baz);
  function new();
    Baz baz;
    super.new();
    baz = new;
    super.m_val = baz;
  endfunction

  task update_value(Foo foo, bit [1:0] val);
    m_val.m_sus[1:0] = val;
  endtask
endclass

module test();
  initial begin
    Foo foo = new;

    for (int i = 0; i < 10; i++) begin
      logic [3:0] v;
      foo.update_value(foo, i[1:0]);
      v = foo.m_val.m_sus;
      if (v[1:0] != i[1:0]) $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
