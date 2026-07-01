// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class FooQ;
  rand int q[$];
endclass

class FooU;
  rand int u[3];
endclass

class FooD;
  rand int d[];
endclass

class FooA;
  rand int a[string];
endclass

class FooW;
  rand int w[*];
endclass

class Inner;
  rand int x;
  constraint c_in {x > 0;}
endclass

class Outer;
  rand Inner inner;
endclass

module t;
  initial begin
    automatic FooQ fq = new;
    automatic FooU fu = new;
    automatic FooD fd = new;
    automatic FooA fa = new;
    automatic FooW fw = new;
    automatic Outer o = new;
    o.inner = new;
    void'(fq.randomize(null));
    void'(fu.randomize(null));
    void'(fd.randomize(null));
    void'(fa.randomize(null));
    void'(fw.randomize(null));
    void'(o.randomize(null));
  end
endmodule
