// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Baz;
endclass

class Bar#(type T) extends T;
endclass

class Foo;
  typedef struct {
    int field;
  } Zee;

  task t1();
    // Refer to Baz CLASSREFDTYPE node in implementation (via CLASSEXTENDS)
    Bar#(Baz) b = new;
  endtask
  // Refer to the very same Baz CLASSREFDTYPE node again, this time within interface
  task t2(Bar#(Baz)::T b);
  endtask
endclass

class Moo;
  // Use Foo::Zee to cause inclusion of Foo's header file
  Foo::Zee z;
endclass

module t();
  initial begin
    // Use Moo in top module to add Moo to root, causing inclusion of Foo header into
    // root header.
    Moo moo;
    moo = new;
  end
endmodule
