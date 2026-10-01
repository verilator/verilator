// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// $typename of a class gives the scope declaring the class (IEEE 1800-2023 20.6.1), the values
// of its parameters, which distinguish its specializations (8.25), and the classes it extends.
// The IEEE leaves the form open, which here is like that of other simulators.

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef enum {
  RED,
  GREEN = 5,
  BLUE
} color_e;
typedef enum logic [1:0] {
  LX = 2'bxx,
  L1 = 2'b01
} lx_e;
typedef struct packed {
  logic [3:0] a;
  bit b;
} ps_t;
typedef struct {
  int a;
  int b;
} us_t;
typedef int iq_t[$];
typedef int bq_t[$:3];
typedef int ua_t[2];
typedef int dyn_t[];
typedef int aa_t[string];
typedef int wild_t [*];
typedef byte wildb_t [*];
typedef int arr_t[4];

// An array with all but one element left as initialized, so given by default
function automatic arr_t arr_one(int value);
  arr_t result;
  result[1] = value;
  return result;
endfunction

class Xyz;
endclass

class Bar #(
    type T = int
);
endclass

// Extends its type parameter
class Foo #(
    type T = Xyz,
    int W = 1
) extends T;
endclass

class Child extends Xyz;
endclass

class GrandChild extends Child;
endclass

class Base #(
    int N = 1
);
endclass

// Extends a specialization with a value computed from its own parameter
class Derived #(
    int M = 2
) extends Base #(M + 1);
endclass

class Values #(
    int I = 1,
    bit [7:0] B = 8'h0f,
    logic [3:0] L = 4'b10xz,
    string S = "hi",
    real R = 1.5,
    color_e E = RED,
    int unsigned U = 3,
    longint LI = 5,
    byte BY = 8'h80
);
endclass

class Aggregates #(
    us_t US = '{1, 2},
    int A[2] = '{3, 4},
    arr_t F = arr_one(5)
);
endclass

// Named exactly, with 17 digits if 15 are not enough, and as a real if a whole number
class Reals #(
    real R = 0.1 + 0.2,
    real E = 1e20,
    real W = 2.0
);
endclass

// Values not of an enum item, of an enum with an unknown item, of a packed structure, and null
class Others #(
    color_e E = color_e'(3),
    lx_e LE = L1,
    ps_t PS = '{4'h3, 1'b1},
    Xyz H = null
);
endclass

// Classes within a class are named within its specialization
class Outer #(
    int P = 1
);
  typedef byte item_t;
  class Inner;
    int v;
    class Deep;
    endclass
    Deep deep;
    covergroup inner_cg;
      coverpoint v;
    endgroup
    function new();
      inner_cg = new;
    endfunction
    // From within the class
    function string name();
      return $typename(this);
    endfunction
  endclass
  class Sub extends Inner;
  endclass
endclass

// A default referring back to the class itself, which not all simulators accept
class SelfRef #(
    type T = SelfRef
);
endclass

interface class Ifc1;
endclass

interface class Ifc2 extends Ifc1;
endclass

class Impl extends Child implements Ifc2;
endclass

class OnlyImpl implements Ifc1;
endclass

class Holder #(
    type T = int
);
  // As an elaboration-time constant (IEEE 1800-2023 20.6.1), which not all simulators accept,
  // so named while the class is specialized
  localparam string TNAME = $typename(T);
endclass

class CgBase #(
    int N = 1
);
  int base_v = N;
  covergroup base_cg;
    coverpoint base_v;
  endgroup
  function new();
    base_cg = new;
  endfunction
endclass

// A covergroup, with arguments, in a parameterized class extending a parameterized class. A
// covergroup in a class is of an anonymous type (IEEE 1800-2023 19.4), named as its variable.
class CgHolder #(
    type T = int,
    int W = 2
) extends CgBase #(W + 1);
  T v;
  covergroup cg(T lo, T hi);
    coverpoint v iff (v >= lo && v <= hi);
  endgroup
  function new();
    super.new();
    cg = new(0, T'(W));
  endfunction
  // From within the class declaring the covergroup
  function string cg_typename();
    return $typename(cg);
  endfunction
endclass

// A covergroup not in any class
covergroup UnitCg with function sample (int s);
  coverpoint s;
endgroup

package pkg;
  class Pc #(
      int N = 3
  );
  endclass
  class Po;
    class Pi;
      class Deep;
      endclass
    endclass
    class Pp #(
        int N = 1
    );
    endclass
  endclass
endpackage

interface ifc #(
    int W = 4
);
  logic [W-1:0] d;
  modport mp(input d);
endinterface

// Defaulting to a specialized interface, and to a type in a specialized class
class Defaults #(
    int X = 1,
    type V = virtual ifc #(8),
    type T = Outer#(5)::item_t,
    Outer#(5)::item_t Y = 3
);
endclass

// Containing a type parameter
class Cont #(
    type E = Xyz
);
  typedef E eq_t[$];
endclass

typedef Bar#(Xyz) bar_xyz_t;
typedef Foo#(Bar#(Xyz), 88) foo_t;

module t;
  class Mcls;
    class Mi;
    endclass
  endclass

  int cg_value;
  // A covergroup in a module
  covergroup ModCg;
    coverpoint cg_value;
  endgroup

  ifc i4 ();
  ifc #(8) i8 ();

  foo_t foo;
  Foo foo_default;
  Bar bar_default;
  bar_xyz_t bar_xyz;
  Bar #(Bar #(Xyz)) bar_bar;
  GrandChild grand;
  Derived #(5) derived;
  Values values_default;
  Values #(-5, 8'hA5, 4'b1x0z, "hello", 0.1, BLUE, 7, 64'h1_0000_0000, 8'h7f) values;
  Aggregates aggregates;
  Reals reals;
  Others others;
  Outer #(7)::Inner inner;
  Outer #(7)::Sub sub;
  pkg::Po::Pi pkg_inner;
  pkg::Po::Pi::Deep pkg_deep;
  pkg::Po::Pp #(4) pkg_param;
  Mcls::Mi mod_inner;
  SelfRef self_ref;
  Impl impl;
  OnlyImpl only_impl;
  Ifc2 ifc2;
  pkg::Pc #(7) pc;
  Mcls mcls;
  Bar #(Mcls) bar_mcls;
  Bar #(int unsigned) bar_uint;
  Bar #(logic signed [6:0]) bar_signed;
  Bar #(iq_t) bar_queue;
  Bar #(bq_t) bar_bqueue;
  Bar #(ua_t) bar_unpack;
  Bar #(dyn_t) bar_dyn;
  Bar #(aa_t) bar_assoc;
  Bar #(wild_t) bar_wild;
  Bar #(wildb_t) bar_wildb;
  Bar #(Cont #(Base #(3))::eq_t) bar_cont;
  Bar #(color_e) bar_enum;
  Bar #(ps_t) bar_struct;
  Bar #(string) bar_string;
  Bar #(real) bar_real;
  Bar #(virtual ifc) bar_vif;
  Bar #(virtual ifc #(8)) bar_vif8;
  virtual ifc.mp vif_mp;
  Child children[2];
  std::mailbox #(int) mbox;
  CgHolder #(byte, 5) cg_holder;
  CgHolder cg_default;
  UnitCg unit_cg;
  ModCg mod_cg;
  Defaults #(2) defaults;

  initial begin
    // The example of issue #8568
    `checks($typename(foo),
            "class{}$unit::Foo#(class{}$unit::Bar#(class{}$unit::Xyz),88) extends class{}$unit::Bar#(class{}$unit::Xyz)");
    `checks($typename(foo_t), $typename(foo));
    `checks($typename(foo_default),
            "class{}$unit::Foo#(class{}$unit::Xyz,1) extends class{}$unit::Xyz");
    `checks($typename(bar_default), "class{}$unit::Bar#(int)");
    `checks($typename(bar_xyz), "class{}$unit::Bar#(class{}$unit::Xyz)");
    `checks($typename(bar_bar), "class{}$unit::Bar#(class{}$unit::Bar#(class{}$unit::Xyz))");
    `checks($typename(grand),
            "class{}$unit::GrandChild extends class{}$unit::Child extends class{}$unit::Xyz");
    `checks($typename(derived), "class{}$unit::Derived#(5) extends class{}$unit::Base#(6)");
    `checks($typename(values_default),
            "class{}$unit::Values#(1,15,4'b10xz,\"hi\",1.5,RED,3,5,-128)");
    `checks($typename(values),
            "class{}$unit::Values#(-5,165,4'b1x0z,\"hello\",0.1,BLUE,7,4294967296,127)");
    `checks($typename(aggregates), "class{}$unit::Aggregates#('{1,2},'{3,4},'{1:5,default:0})");
    `checks($typename(reals), "class{}$unit::Reals#(0.30000000000000004,1e+20,2.0)");
    `checks($typename(others), "class{}$unit::Others#(3,L1,7,null)");
    `checks($typename(inner), "class{}$unit::Outer#(7)::Inner");
    // Classes within a class (within a class)
    inner = new;
    `checks(inner.name(), "class{}$unit::Outer#(7)::Inner");
    `checks($typename(inner.deep), "class{}$unit::Outer#(7)::Inner::Deep");
    `checks($typename(inner.inner_cg), "class{}$unit::Outer#(7)::Inner::inner_cg");
    `checks($typename(sub), "class{}$unit::Outer#(7)::Sub extends class{}$unit::Outer#(7)::Inner");
    `checks($typename(pkg_inner), "class{}pkg::Po::Pi");
    `checks($typename(pkg_deep), "class{}pkg::Po::Pi::Deep");
    `checks($typename(pkg_param), "class{}pkg::Po::Pp#(4)");
    `checks($typename(mod_inner), "class{}t.Mcls::Mi");
    `checks($typename(self_ref), "class{}$unit::SelfRef#(class{}$unit::SelfRef)");
    // Implementing an interface class is not extending it
    `checks($typename(impl),
            "class{}$unit::Impl extends class{}$unit::Child extends class{}$unit::Xyz");
    `checks($typename(only_impl), "class{}$unit::OnlyImpl");
    `checks($typename(ifc2), "class{}$unit::Ifc2");
    `checks($typename(pc), "class{}pkg::Pc#(7)");
    `checks($typename(mcls), "class{}t.Mcls");
    `checks($typename(bar_mcls), "class{}$unit::Bar#(class{}t.Mcls)");
    `checks($typename(bar_uint), "class{}$unit::Bar#(int unsigned)");
    `checks($typename(bar_signed), "class{}$unit::Bar#(logic signed[6:0])");
    `checks($typename(bar_queue), "class{}$unit::Bar#(int$[$])");
    `checks($typename(bar_bqueue), "class{}$unit::Bar#(int$[$:3])");
    `checks($typename(bar_unpack), "class{}$unit::Bar#(int$[0:1])");
    `checks($typename(bar_dyn), "class{}$unit::Bar#(int$[])");
    `checks($typename(bar_assoc), "class{}$unit::Bar#(int$[string])");
    `checks($typename(bar_wild), "class{}$unit::Bar#(int$[*])");
    `checks($typename(bar_wildb), "class{}$unit::Bar#(byte$[*])");
    `checks($typename(bar_cont), "class{}$unit::Bar#(class{}$unit::Base#(3)$[$])");
    `checks($typename(bar_enum),
            "class{}$unit::Bar#(enum{RED=32'h0;GREEN=32'h5;BLUE=32'h6;}$unit::color_e)");
    `checks($typename(bar_struct), "class{}$unit::Bar#(struct{logic[3:0] a;bit b;}$unit::ps_t)");
    `checks($typename(bar_string), "class{}$unit::Bar#(string)");
    `checks($typename(bar_real), "class{}$unit::Bar#(real)");
    `checks($typename(bar_vif), "class{}$unit::Bar#(virtual interface ifc#(4))");
    `checks($typename(bar_vif8), "class{}$unit::Bar#(virtual interface ifc#(8))");
    `checks($typename(vif_mp), "virtual interface ifc#(4).mp");
    // Within another type, a class is named without the classes it extends
    `checks($typename(children), "class{}$unit::Child$[0:1]");
    `checks($typename(mbox), "class{}std::mailbox#(int)");
    cg_holder = new;
    cg_default = new;
    `checks($typename(cg_holder),
            "class{}$unit::CgHolder#(byte,5) extends class{}$unit::CgBase#(6)");
    `checks($typename(cg_holder.cg), "class{}$unit::CgHolder#(byte,5)::cg");
    `checks(cg_holder.cg_typename(), $typename(cg_holder.cg));
    `checks($typename(cg_default.cg), "class{}$unit::CgHolder#(int,2)::cg");
    `checks($typename(cg_holder.base_cg), "class{}$unit::CgBase#(6)::base_cg");
    unit_cg = new;
    mod_cg = new;
    unit_cg.sample(1);
    mod_cg.sample();
    `checks($typename(unit_cg), "class{}$unit::UnitCg");
    `checks($typename(mod_cg), "class{}t.ModCg");
    `checks($typename(defaults), "class{}$unit::Defaults#(2,virtual interface ifc#(8),byte,3)");
    // As named while being specialized
    `checks(Holder#(bar_xyz_t)::TNAME, $typename(bar_xyz_t));
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
