// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand int unsigned a;
  rand int unsigned b;
  int x;

  function new(int x);
    this.x = x;
  endfunction

  constraint constr1_c { b < x; }
endclass

class Bar;
  // Give the local variables a different scope by defining the functino under Bar
  static function bit test_local_constrdep(Foo foo, int c);
    return foo.randomize() with { a <= c; a > 1; x % a == 0; } == 1;
  endfunction
endclass

module submodule();
  int sub_var = 7;
endmodule

module mwith();
  submodule sub1();
  submodule sub2();

  initial begin
    int c = 30;
    Foo foo = new(c);
    $display("foo.x = %d", foo.x);
    $display("-----------------");

    repeat (20) begin
      if (Bar::test_local_constrdep(foo, 5)) begin
        $display("foo.a = %d", foo.a);
        $display("foo.b = %d", foo.b);
        $display("-----------------");

        if (!(foo.a inside {2, 3, 5})) $stop;
        if (foo.b >= foo.x) $stop;
        if (foo.a > c) $stop;
        if (foo.a <= 1) $stop;

        sub1.sub_var = foo.a;
      end else
        $display("Failed to randomize foo with inline constraints");
    end

    // Check capture of a static variable
    if (foo.randomize() with { a > sub1.sub_var; } != 1) $stop;

    $write("*-* All Finished *-*\n");
    $finish();
  end
endmodule
