// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   void'(cl.randomize()); \
   prev_result = longint'(field); \
   repeat(9) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class Boo;
  function new();
    boo = 6;
  endfunction

  int unsigned boo;
endclass

class Foo extends Boo;
  rand int unsigned a;
  rand int unsigned b;
  int x;

  function new(int x);
    this.x = x;
  endfunction

  constraint constr1_c { b < x; }
  function bit test_this_randomize;
    return this.randomize() with { a <= boo; } == 1;
  endfunction
endclass

// Current AstWith representation makes VARs of caller indistinguishable from VARs of randomized
// object if both the caller and callee are the same module, but different instances.
// That's why for the purpose of this test, the caller derives a different class
class Bar extends Boo;
  // Give the local variables a different scope by defining the functino under Bar
  static function bit test_local_constrdep(Foo foo, int c);
    return foo.randomize() with { a <= c; a > 1; x % a == 0; } == 1;
  endfunction

  function bit test_capture_of_callers_derived_var(Foo foo);
    boo = 4;
    foo.a = 3;
    return (foo.randomize() with { a == local::boo; } == 1) && (foo.a == 4);
  endfunction

  static function bit test_capture_of_callees_derived_var(Foo foo);
    foo.a = 5;
    return (foo.randomize() with { a == boo; } == 1) && (foo.a == 6);
  endfunction

  static function bit test_capture_of_local_qualifier(Foo foo);
    foo.a = 5;
    return (foo.randomize() with { a == boo; } == 1) && (foo.a == 6);
  endfunction
endclass

class Baz;
  rand int v;
endclass

class Baz2;
  rand int v;
  function bit test_this_randomize;
    return this.randomize() with { v == 5; } == 1;
  endfunction
endclass

module submodule();
  int sub_var = 7;
endmodule

function automatic int return_2();
  return 2;
endfunction

class Cls;
   rand int a;
   rand int b;
endclass

class Cls2 extends Cls;
   rand int c;
endclass

module mwith();
  submodule sub1();
  submodule sub2();

  function automatic int return_3();
    return 3;
  endfunction

  initial begin
    int c = 30;
    Foo foo = new(c);
    Baz baz = new;
    Baz2 baz2 = new;
    Bar bar = new;
    Cls2 cls2 = new;
    Cls cls = cls2;
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

    if (cls.randomize() with { b == 1;} != 1) $stop;
    if (cls.b != 1) $stop;
    `check_rand(cls2, cls2.a);
    `check_rand(cls2, cls2.c);

    // Check randomize as a task
    // verilator lint_off IGNOREDRETURN
    cls.randomize() with { b == 2;};
    // verilator lint_on IGNOREDRETURN
    if (cls.b != 2) $stop;

    // Check capture of a static variable
    if (foo.randomize() with { a > sub1.sub_var; } != 1) $stop;
    // Check reference to a function
    if (foo.randomize() with { a > return_2(); } != 1) $stop;
    // Check randomization of class with no constraints
    if (baz.randomize() with { v inside {[2:10]}; } != 1) $stop;
    // Check randomization with captured non-static variable from different AstNodeModule
    if (!bar.test_capture_of_callers_derived_var(foo)) $stop;
    // Check randomization with non-captured non-static variable from different AstNodeModule
    if (!Bar::test_capture_of_callees_derived_var(foo)) $stop;
    // Check this.randomize()
    if (!foo.test_this_randomize()) $stop;
    // Check this.randomize() with no constraints
    if (!baz2.test_this_randomize()) $stop;

    $write("*-* All Finished *-*\n");
    $finish();
  end
endmodule
