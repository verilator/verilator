// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// See also t_class_param.v

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Parcls #(
    type T
);
  static function int get_p;
    return T::get_p();
  endfunction
endclass

class Cls;
  static function int get_p;
    return 20;
  endfunction
endclass

class ParclsDefaultType #(
    type T = Cls
);
  static function int get_p;
    return T::get_p();
  endfunction
endclass

typedef Cls cls_t;
typedef cls_t cls2_t;

class Singleton #(
    type T = int
);
  static function Singleton#(T) self;
    static Singleton #(T) c = new;
    return c;
  endfunction
  function int get_size;
    return $bits(T);
  endfunction
endclass

class SingletonUnusedDefault #(
    type T = int
);
  static function SingletonUnusedDefault#(T) self;
    static SingletonUnusedDefault #(T) c = new;
    return c;
  endfunction
endclass

class Empty;
endclass

class Foo #(
    type IF = Empty
) extends IF;
  typedef Foo foo_t;
  int a = 1;
endclass

class Bar #(
    type A = int,
    type B = A
) extends Foo #();
  function int get_size_A;
    return $bits(A);
  endfunction
  function int get_size_B;
    return $bits(B);
  endfunction
endclass

class Empty2;
endclass

class Baz #(
    type T = Empty2
) extends Foo #();
endclass

class Getter1 extends Baz #();
  function int get_1;
    foo_t f = new;
    return f.a;
  endfunction
endclass

class MyInt1;
  int x = 1;
endclass

class MyInt2;
  int x = 2;
endclass

class ExtendsMyInt #(
    type T = MyInt1
) extends T;
  typedef ExtendsMyInt#(T) this_type;
  function int get_this_type_x;
    this_type t = new;
    return t.x;
  endfunction
endclass

class StaticX;
  static int val = 1;
endclass

class GetStaticXVal #(
    type T = int
);
  static function int get;
    return T::val;
  endfunction
endclass

typedef bit [6:0] bit7_t;
typedef bit [14:0] bit15_t;

class Outside #(type U = int);
  U value;
endclass

class Self #(type T = int);
  T value;

  class Inner #(type U = int);
    U value;
  endclass

  static Inner #(T) scope_nested = new;
  static Outside #(T) scope_external = new;
  static Self #(T) scope_self = new;

  static function Inner#(T) nested_factory();
    Inner #(T) obj = new;
    return obj;
  endfunction

  static function Outside#(T) external_factory();
    Outside #(T) obj = new;
    return obj;
  endfunction

  static function Self#(T) self_factory();
    Self #(T) obj = new;
    return obj;
  endfunction

  static function Self#(bit15_t) wide_factory();
    Self #(bit15_t) obj = new;
    return obj;
  endfunction

  function void check_objects(int data, int width, int mask);
    Inner #(T) runtime_nested = new;
    Outside #(T) runtime_external = new;
    Self #(T) runtime_self = new;
    Inner #(T) factory_nested = nested_factory();
    Outside #(T) factory_external = external_factory();
    Self #(T) factory_self = self_factory();
    Self #(bit15_t) runtime_wide = new;
    Self #(bit15_t) factory_wide = wide_factory();

    scope_nested.value = T'(data + 1);
    scope_external.value = T'(data + 2);
    scope_self.value = T'(data + 3);
    runtime_nested.value = T'(data + 4);
    runtime_external.value = T'(data + 5);
    runtime_self.value = T'(data + 6);
    factory_nested.value = T'(data + 7);
    factory_external.value = T'(data + 8);
    factory_self.value = T'(data + 9);
    runtime_wide.value = bit15_t'(data + 10);
    factory_wide.value = bit15_t'(data + 11);

    `checkd($bits(scope_nested.value), width);
    `checkd(int'(scope_nested.value), (data + 1) & mask);
    `checkd($bits(scope_external.value), width);
    `checkd(int'(scope_external.value), (data + 2) & mask);
    `checkd($bits(scope_self.value), width);
    `checkd(int'(scope_self.value), (data + 3) & mask);
    `checkd($bits(runtime_nested.value), width);
    `checkd(int'(runtime_nested.value), (data + 4) & mask);
    `checkd($bits(runtime_external.value), width);
    `checkd(int'(runtime_external.value), (data + 5) & mask);
    `checkd($bits(runtime_self.value), width);
    `checkd(int'(runtime_self.value), (data + 6) & mask);
    `checkd($bits(factory_nested.value), width);
    `checkd(int'(factory_nested.value), (data + 7) & mask);
    `checkd($bits(factory_external.value), width);
    `checkd(int'(factory_external.value), (data + 8) & mask);
    `checkd($bits(factory_self.value), width);
    `checkd(int'(factory_self.value), (data + 9) & mask);
    `checkd($bits(runtime_wide.value), 15);
    `checkd(int'(runtime_wide.value), (data + 10) & 'h7fff);
    `checkd($bits(factory_wide.value), 15);
    `checkd(int'(factory_wide.value), (data + 11) & 'h7fff);
  endfunction
endclass

module t(
    input clk
);

  int cycles = 0;
  always @(posedge clk) cycles <= cycles + 1;

  Self #(int) owner_int = new;
  Self #(bit7_t) owner_bit7 = new;

  always @(negedge clk) begin
    int data;
    data = (cycles << 17) | (cycles << 9) | cycles;
    owner_int.check_objects(data, 32, 'hffffffff);
    owner_bit7.check_objects(data + 37, 7, 'h7f);
    // Reread after both specializations have written their static objects.
    `checkd(int'(Self#(int)::scope_nested.value), data + 1);
    `checkd(int'(Self#(int)::scope_external.value), data + 2);
    `checkd(int'(Self#(int)::scope_self.value), data + 3);
    `checkd(int'(Self#(bit7_t)::scope_nested.value), (data + 38) & 'h7f);
    `checkd(int'(Self#(bit7_t)::scope_external.value), (data + 39) & 'h7f);
    `checkd(int'(Self#(bit7_t)::scope_self.value), (data + 40) & 'h7f);
    if (cycles == 32) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  initial begin
    automatic ParclsDefaultType #(Cls) pdt1 = new;
    automatic ParclsDefaultType #(cls_t) pdt2 = pdt1;
    automatic ParclsDefaultType #(cls2_t) pdt3 = pdt2;
    automatic Parcls #(Cls) p1 = new;
    automatic Parcls #(cls_t) p2 = p1;
    automatic Parcls #(cls2_t) p3 = p2;

    automatic Singleton #(int) s_int1 = Singleton#(int)::self();
    automatic Singleton #(int) s_int2 = Singleton#(int)::self();
    automatic Singleton #(bit) s_bit1 = Singleton#(bit)::self();
    automatic Singleton #(bit) s_bit2 = Singleton#(bit)::self();
    automatic SingletonUnusedDefault #(bit) sud1 = SingletonUnusedDefault#(bit)::self();
    automatic SingletonUnusedDefault #(bit) sud2 = SingletonUnusedDefault#(bit)::self();

    automatic Getter1 getter1 = new;

    automatic ExtendsMyInt #() ext1 = new;
    automatic ExtendsMyInt #(MyInt2) ext2 = new;

    automatic GetStaticXVal #(StaticX) get_statix_x_val = new;

    typedef bit my_bit_t;
    automatic Bar #(.A(my_bit_t)) bar_a_bit = new;
    automatic Bar #(.B(my_bit_t)) bar_b_bit = new;
    automatic Bar #() bar_default = new;

    if (bar_a_bit.get_size_A != 1) $stop;
    if (bar_a_bit.get_size_B != 1) $stop;
    if (bar_b_bit.get_size_A != 32) $stop;
    if (bar_b_bit.get_size_B != 1) $stop;
    if (bar_default.get_size_A != 32) $stop;
    if (bar_default.get_size_B != 32) $stop;

    if (pdt1 != pdt2) $stop;
    if (pdt2 != pdt3) $stop;
    if (p1 != p2) $stop;
    if (p2 != p3) $stop;

    if (s_int1 != s_int2) $stop;
    if (s_bit1 != s_bit2) $stop;
    if (sud1 != sud2) $stop;

    if (s_int1.get_size() != 32) $stop;
    if (s_bit1.get_size() != 1) $stop;

    if (p1.get_p() != 20) $stop;
    if (pdt1.get_p() != 20) $stop;
    if (Parcls#(cls2_t)::get_p() != 20) $stop;

    if (getter1.get_1() != 1) $stop;

    if (ext1.get_this_type_x() != 1) $stop;
    if (ext2.get_this_type_x() != 2) $stop;

    if (get_statix_x_val.get() != 1) $stop;
  end
endmodule
