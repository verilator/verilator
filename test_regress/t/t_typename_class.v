// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// $typename of a class gives the scope declaring the class (IEEE 1800-2023 20.6.1), the values
// of its parameters, which distinguish its specializations (8.25), and the class it extends,
// though not the classes that one extends, which $typename of that class gives.
// 20.6.1 does not give the form of these, which here is like that of other simulators.
// A structure, union, or enumeration is likewise named with the scope declaring it. For
// readability, it is named without its members or items, so unlike the examples of 20.6.1,
// without the values of the items of an enumeration.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
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
typedef union packed {
  logic [7:0] b;
  bit [7:0] c;
} pu_t;
typedef struct {
  int a;
  int b;
} us_t;
typedef int int_t;
// Of an escaped name, named escaped, as in hierarchical names (IEEE 1800-2023 23.6)
typedef struct packed {bit a;} \esc.s_t ;
// Of several types, and of another structure
typedef struct {
  int_t i;
  ps_t ps;
  color_e c;
  string s;
  real r;
  bit [7:0] v[2];
} nested_t;
typedef int iq_t[$];
typedef int bq_t[$:3];
typedef int ua_t[2];
typedef int dyn_t[];
typedef int aa_t[string];
typedef int wild_t [*];
typedef byte wildb_t [*];
typedef int arr_t[4];

typedef int a58_t[5:8];
typedef int a85_t[8:5];
typedef int an_t[-1:1];

// An array with all but one element left as initialized, so given by default
function automatic arr_t arr_one(int value);
  arr_t result;
  result[1] = value;
  return result;
endfunction
// Likewise, of arrays not indexed from 0
function automatic a58_t a58_one(int value);
  a58_t result;
  result[6] = value;
  return result;
endfunction
function automatic a85_t a85_two(int value7, int value6);
  a85_t result;
  result[6] = value6;
  result[7] = value7;
  return result;
endfunction
function automatic an_t an_one(int value);
  an_t result;
  result[-1] = value;
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

class GreatGrandChild extends GrandChild;
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

// Likewise, extending such a class
class Derived2 #(
    int K = 3
) extends Derived #(K * 2);
endclass

// Extending a specialization by its type parameter, and likewise extending such a class
class Wrap #(
    type T = Xyz
) extends Bar #(T);
endclass

class Wrap2 #(
    type T = Xyz
) extends Wrap #(T);
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

// Elements listed from the left index, and indexed as declared
class Ranges #(
    int D[1:0] = '{10, 20},
    int N[-1:1] = '{7, 8, 9},
    a58_t U = a58_one(9),
    a85_t W = a85_two(1, 2),
    an_t M = an_one(4)
);
endclass

// Strings, which a name shows escaped, and whatever they contain
class StrP #(
    string S = ""
);
endclass

class Str2 #(
    string A = "",
    string B = ""
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
  typedef struct packed {logic [W-1:0] d;} is_t;
endinterface

// Structures of types given by the parameters, named within the specialization
class Ps #(
    int W = 4
);
  typedef struct packed {logic [W-1:0] d;} s_t;
  typedef enum logic [W-1:0] {
    P0,
    P1
  } e_t;
  s_t s;
  function string s_typename();
    return $typename(s);
  endfunction
  // Declared within a function, still within the specialization
  function string local_typename();
    typedef struct packed {logic [W-1:0] l;} local_t;
    local_t l;
    return $typename(l);
  endfunction
endclass

// Likewise within a module, and an interface
module msub #(
    parameter int W = 4
);
  typedef struct packed {logic [W-1:0] d;} ms_t;
  ms_t v;
  ifc #(W) i ();
  typedef i.is_t ms_is_t;
  ms_is_t iv;
  function automatic string ms_typename();
    return $typename(v);
  endfunction
  function automatic string is_typename();
    return $typename(iv);
  endfunction
endmodule

// Of a type parameter, so named with the type, once resolved, as of the default
module mtsub #(
    parameter type T = int
);
  typedef struct packed {T d;} mt_t;
  mt_t v;
  function automatic string mt_typename();
    return $typename(v);
  endfunction
endmodule

// Of a module without a parameter port list, whose parameters may so follow a type its name holds
module mbody;
  typedef struct packed {logic a;} mb_t;
  parameter type T = int;
  mb_t v;
  function automatic string mb_typename();
    return $typename(v);
  endfunction
endmodule

// Likewise of a class, named before the parameter is widthed
module mcbody;
  class MBC;
  endclass
  MBC c;
  function automatic string c_typename();
    return $typename(c);
  endfunction
  parameter int W = 3;
endmodule

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

// Giving another module a type of its type parameter
class TypeP #(
    type T = int
);
  typedef T elem_t;
endclass

interface tifc #(
    type T = int
);
  T v;
endinterface

// A class within a module, of which each specialization has its own
module mcls #(
    parameter int W = 4
);
  class MC;
  endclass
  MC mc;
  function automatic string mc_typename();
    return $typename(mc);
  endfunction
endmodule

// Likewise within an interface
interface cifc #(
    int W = 4
);
  class IC;
  endclass
  IC ic;
  function automatic string ic_typename();
    return $typename(ic);
  endfunction
endinterface

typedef Bar#(Xyz) bar_xyz_t;
typedef Foo#(Bar#(Xyz), 88) foo_t;
typedef StrP#("__DOT__x") strp_dot_t;
typedef Ps#(8)::s_t ps8_s_t;

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

  // Types in generate blocks, named with each block, as each is a scope (IEEE 1800-2023 27.6)
  for (genvar i = 0; i < 2; ++i) begin : gen
    typedef struct packed {bit a;} gs_t;
    gs_t gs;
    covergroup GenCg;
      coverpoint cg_value;
    endgroup
    GenCg gen_cg = new;
  end
  // The unnamed block around the 'if' of an 'else if' is not a scope
  if (0) begin : gen_if
  end
  else if (1) begin : gen_elif
    typedef struct packed {bit b;} ge_t;
    ge_t ge;
  end

  ifc i4 ();
  ifc #(8) i8 ();
  msub u4 ();
  msub #(16) u16 ();
  mtsub mt_int ();
  mtsub #(byte) mt_byte ();
  mbody mb_int ();
  mbody #(.T(byte)) mb_byte ();
  mcbody mcb3 ();
  mcbody #(.W(5)) mcb5 ();
  mcls mc4 ();
  mcls #(16) mc16 ();
  cifc ci4 ();
  cifc #(16) ci16 ();
  tifc #(byte) tb ();

  // Not classes, named as resolved (IEEE 1800-2023 20.6.1), and a structure without its members
  typedef struct packed {
    ps_t ps;
    logic signed [2:0] q;
  } mps_t;
  int_t int_value;
  nested_t nested;
  mps_t mps;
  localparam nested_t NESTED = '{
      i: 3,
      ps: '{a: 4'h5, b: 1'b1},
      c: GREEN,
      s: "x",
      r: 1.5,
      v: '{8'h1, 8'h2}
  };
  Bar #(int_t) bar_int;
  // Of a type given by parameters
  Ps ps_default;
  Ps #(8) ps8;
  Ps #(8)::s_t ps8_s;
  Bar #(Ps #(8)::s_t) bar_ps8_s;
  Ps #(8)::e_t ps8_e;
  Bar #(Ps #(8)::e_t) bar_ps8_e;
  Bar #(Ps #(16)::e_t) bar_ps16_e;
  Ps #(8)::s_t ps8_sa[2];
  Ps #(16)::s_t ps16_sa[2];
  Ps #(8)::s_t ps8_sq[$];
  ps8_s_t ps8_s_td;
  // Of a type parameter only given by the type of another module
  TypeP #(byte)::elem_t typep_elem;
  TypeP #(byte) typep;
  virtual tifc #(byte) vtb;
  Ranges ranges;
  StrP #("__DOT__x") strp_dot;
  strp_dot_t strp_dot_td;
  StrP #("a\"b") strp_quote;
  StrP #("t\tn\n") strp_ctrl;
  Str2 #("a\",\"b", "c") str2_ab;
  Str2 #("a", "b\",\"c") str2_bc;

  foo_t foo;
  Foo foo_default;
  Bar bar_default;
  bar_xyz_t bar_xyz;
  Bar #(Bar #(Xyz)) bar_bar;
  GrandChild grand;
  GreatGrandChild great_grand;
  Derived #(5) derived;
  Derived #(6) derived6;
  Derived2 derived2;
  Foo #(Child, 3) foo_child;
  // Of classes extending several levels of classes, as parameters
  Bar #(Derived2 #(4)) bar_derived2;
  Foo #(Derived2 #(4), 9) foo_derived2;
  Wrap2 #(Derived2 #(4)) wrap2;
  Bar #(Wrap2 #(Derived2 #(4))) bar_wrap2;
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
  Bar #(pu_t) bar_union;
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
            "class $unit::Foo#(class $unit::Bar#(class $unit::Xyz),88) extends class $unit::Bar#(class $unit::Xyz)");
    `checks($typename(foo_t), $typename(foo));
    `checks($typename(foo_default),
            "class $unit::Foo#(class $unit::Xyz,1) extends class $unit::Xyz");
    `checks($typename(bar_default), "class $unit::Bar#(int)");
    `checks($typename(bar_xyz), "class $unit::Bar#(class $unit::Xyz)");
    `checks($typename(bar_bar), "class $unit::Bar#(class $unit::Bar#(class $unit::Xyz))");
    // Only the class it extends, as $typename of that class names the classes that one extends
    `checks($typename(grand), "class $unit::GrandChild extends class $unit::Child");
    `checks($typename(Child), "class $unit::Child extends class $unit::Xyz");
    `checks($typename(great_grand), "class $unit::GreatGrandChild extends class $unit::GrandChild");
    `checks($typename(derived), "class $unit::Derived#(5) extends class $unit::Base#(6)");
    `checks($typename(derived2), "class $unit::Derived2#(3) extends class $unit::Derived#(6)");
    `checks($typename(derived6), "class $unit::Derived#(6) extends class $unit::Base#(7)");
    `checks($typename(foo_child),
            "class $unit::Foo#(class $unit::Child,3) extends class $unit::Child");
    // As parameters, classes are named without the classes they extend, at any depth
    `checks($typename(bar_derived2), "class $unit::Bar#(class $unit::Derived2#(4))");
    `checks($typename(foo_derived2),
            "class $unit::Foo#(class $unit::Derived2#(4),9) extends class $unit::Derived2#(4)");
    `checks($typename(wrap2),
            "class $unit::Wrap2#(class $unit::Derived2#(4)) extends class $unit::Wrap#(class $unit::Derived2#(4))");
    `checks($typename(bar_wrap2),
            "class $unit::Bar#(class $unit::Wrap2#(class $unit::Derived2#(4)))");
    `checks($typename(values_default),
            "class $unit::Values#(1,15,4'b10xz,\"hi\",1.5,RED,3,5,-128)");
    `checks($typename(values),
            "class $unit::Values#(-5,165,4'b1x0z,\"hello\",0.1,BLUE,7,4294967296,127)");
    `checks($typename(aggregates), "class $unit::Aggregates#('{1,2},'{3,4},'{1:5,default:0})");
    `checks($typename(reals), "class $unit::Reals#(0.30000000000000004,1e+20,2.0)");
    `checks($typename(others), "class $unit::Others#(3,L1,7,null)");
    `checks($typename(inner), "class $unit::Outer#(7)::Inner");
    // Classes within a class (within a class)
    inner = new;
    `checks(inner.name(), "class $unit::Outer#(7)::Inner");
    `checks($typename(inner.deep), "class $unit::Outer#(7)::Inner::Deep");
    `checks($typename(inner.inner_cg), "class $unit::Outer#(7)::Inner::inner_cg");
    `checks($typename(sub), "class $unit::Outer#(7)::Sub extends class $unit::Outer#(7)::Inner");
    `checks($typename(pkg_inner), "class pkg::Po::Pi");
    `checks($typename(pkg_deep), "class pkg::Po::Pi::Deep");
    `checks($typename(pkg_param), "class pkg::Po::Pp#(4)");
    `checks($typename(mod_inner), "class t.Mcls::Mi");
    `checks($typename(self_ref), "class $unit::SelfRef#(class $unit::SelfRef)");
    // Implementing an interface class is not extending it
    `checks($typename(impl), "class $unit::Impl extends class $unit::Child");
    `checks($typename(only_impl), "class $unit::OnlyImpl");
    `checks($typename(ifc2), "class $unit::Ifc2");
    `checks($typename(pc), "class pkg::Pc#(7)");
    `checks($typename(mcls), "class t.Mcls");
    `checks($typename(bar_mcls), "class $unit::Bar#(class t.Mcls)");
    `checks($typename(bar_uint), "class $unit::Bar#(int unsigned)");
    `checks($typename(bar_signed), "class $unit::Bar#(logic signed[6:0])");
    `checks($typename(bar_queue), "class $unit::Bar#(int$[$])");
    `checks($typename(bar_bqueue), "class $unit::Bar#(int$[$:3])");
    `checks($typename(bar_unpack), "class $unit::Bar#(int$[0:1])");
    `checks($typename(bar_dyn), "class $unit::Bar#(int$[])");
    `checks($typename(bar_assoc), "class $unit::Bar#(int$[string])");
    `checks($typename(bar_wild), "class $unit::Bar#(int$[*])");
    `checks($typename(bar_wildb), "class $unit::Bar#(byte$[*])");
    `checks($typename(bar_cont), "class $unit::Bar#(class $unit::Base#(3)$[$])");
    `checks($typename(bar_enum), "class $unit::Bar#(enum $unit::color_e)");
    `checks($typename(bar_struct), "class $unit::Bar#(struct $unit::ps_t)");
    `checks($typename(bar_union), "class $unit::Bar#(union $unit::pu_t)");
    // Without their members, as named by themselves
    `checks($typename(color_e), "enum $unit::color_e");
    `checks($typename(ps_t), "struct $unit::ps_t");
    `checks($typename(pu_t), "union $unit::pu_t");
    `checks($typename(\esc.s_t ), "struct $unit::\\esc.s_t ");
    `checks($typename(bar_enum), {"class $unit::Bar#(", $typename(color_e), ")"});
    `checks($typename(bar_struct), {"class $unit::Bar#(", $typename(ps_t), ")"});
    `checks($typename(bar_union), {"class $unit::Bar#(", $typename(pu_t), ")"});
    `checks($typename(bar_string), "class $unit::Bar#(string)");
    `checks($typename(bar_real), "class $unit::Bar#(real)");
    `checks($typename(bar_vif), "class $unit::Bar#(virtual interface ifc#(4))");
    `checks($typename(bar_vif8), "class $unit::Bar#(virtual interface ifc#(8))");
    `checks($typename(vif_mp), "virtual interface ifc#(4).mp");
    // Within another type, a class is named without the class it extends
    `checks($typename(children), "class $unit::Child$[0:1]");
    `checks($typename(mbox), "class std::mailbox#(int)");
    cg_holder = new;
    cg_default = new;
    `checks($typename(cg_holder), "class $unit::CgHolder#(byte,5) extends class $unit::CgBase#(6)");
    `checks($typename(cg_holder.cg), "class $unit::CgHolder#(byte,5)::cg");
    `checks(cg_holder.cg_typename(), $typename(cg_holder.cg));
    `checks($typename(cg_default.cg), "class $unit::CgHolder#(int,2)::cg");
    `checks($typename(cg_holder.base_cg), "class $unit::CgBase#(6)::base_cg");
    unit_cg = new;
    mod_cg = new;
    unit_cg.sample(1);
    mod_cg.sample();
    `checks($typename(unit_cg), "class $unit::UnitCg");
    `checks($typename(mod_cg), "class t.ModCg");
    `checks($typename(gen[0].gs), "struct t.gen[0].gs_t");
    `checks($typename(gen[1].gs), "struct t.gen[1].gs_t");
    `checks($typename(gen[0].gen_cg), "class t.gen[0].GenCg");
    `checks($typename(gen[1].gen_cg), "class t.gen[1].GenCg");
    `checks($typename(gen_elif.ge), "struct t.gen_elif.ge_t");
    `checks($typename(defaults), "class $unit::Defaults#(2,virtual interface ifc#(8),byte,3)");
    // As named while being specialized, before the types are otherwise named, so for a
    // structure and an enumeration, from their typedefs
    `checks(Holder#(bar_xyz_t)::TNAME, $typename(bar_xyz_t));
    `checks(Holder#(ps_t)::TNAME, $typename(ps_t));
    `checks(Holder#(color_e)::TNAME, $typename(color_e));
    // Not classes
    `checks($typename(int_value), "int");
    `checks($typename(int_t), "int");
    `checks($typename(bar_int), $typename(bar_default));
    `checks($typename(nested), "struct $unit::nested_t");
    `checks($typename(NESTED), $typename(nested));
    `checks($typename(NESTED.ps), "struct $unit::ps_t");
    `checks($typename(nested.i), "int");
    `checks($typename(nested.v), "bit[7:0]$[0:1]");
    `checks($typename(mps), "struct t.mps_t");
    `checks($typename(mps.ps), "struct $unit::ps_t");
    `checks($typename(mps.q), "logic signed[2:0]");
    `checkd(NESTED.ps.a, 4'h5);
    `checks(NESTED.s, "x");
    // Of a type given by parameters
    ps_default = new;
    ps8 = new;
    `checks($typename(ps_default.s), "struct $unit::Ps#(4)::s_t");
    `checks($typename(ps8.s), "struct $unit::Ps#(8)::s_t");
    `checks($typename(ps8_s), "struct $unit::Ps#(8)::s_t");
    `checks(ps8.s_typename(), "struct $unit::Ps#(8)::s_t");
    `checks(ps8.local_typename(), "struct $unit::Ps#(8)::local_t");
    `checks($typename(bar_ps8_s), "class $unit::Bar#(struct $unit::Ps#(8)::s_t)");
    `checks($typename(ps8_e), "enum $unit::Ps#(8)::e_t");
    `checks($typename(bar_ps8_e), {"class $unit::Bar#(", $typename(ps8_e), ")"});
    `checks($typename(bar_ps16_e), "class $unit::Bar#(enum $unit::Ps#(16)::e_t)");
    `checks(u4.ms_typename(), "struct msub#(4).ms_t");
    `checks(u16.ms_typename(), "struct msub#(16).ms_t");
    `checks(u4.is_typename(), "struct ifc#(4).is_t");
    `checks(u16.is_typename(), "struct ifc#(16).is_t");
    `checks(mt_int.mt_typename(), "struct mtsub#(int).mt_t");
    `checks(mt_byte.mt_typename(), "struct mtsub#(byte).mt_t");
    `checks(mb_int.mb_typename(), "struct mbody#(int).mb_t");
    `checks(mb_byte.mb_typename(), "struct mbody#(byte).mb_t");
    `checks(mcb3.c_typename(), "class mcbody#(3).MBC");
    `checks(mcb5.c_typename(), "class mcbody#(5).MBC");
    // Of a data type, named as of a variable of it
    `checks($typename(Ps#(8)::s_t), $typename(ps8_s));
    `checks($typename(Ps#(8)::e_t), $typename(ps8_e));
    `checks($typename(ps8_s_t), $typename(ps8_s));
    `checks($typename(ps8_s_td), $typename(ps8_s));
    // Of arrays of such, whose elements are named likewise
    `checks($typename(ps8_sa), "struct $unit::Ps#(8)::s_t$[0:1]");
    `checks($typename(ps16_sa), "struct $unit::Ps#(16)::s_t$[0:1]");
    `checks($typename(ps8_sa[0]), $typename(ps8_s));
    `checks($typename(ps8_sq[0]), $typename(ps8_s));
    `checks($typename(Ps#(8)::P1), $typename(ps8_e));
    // Of a type parameter only given by the type of another module
    `checks($typename(typep), "class $unit::TypeP#(byte)");
    `checks($typename(typep_elem), "byte");
    `checks($typename(vtb), "virtual interface tifc#(byte)");
    // Of array values, listed from the left index
    `checks($typename(ranges),
            "class $unit::Ranges#('{10,20},'{7,8,9},'{6:9,default:0},'{7:1,6:2,default:0},'{-1:4,default:0})");
    // Of strings, escaped, and not taken as names
    `checks($typename(strp_dot), "class $unit::StrP#(\"__DOT__x\")");
    `checks($typename(strp_dot_td), $typename(strp_dot));
    `checks($typename(strp_dot_t), $typename(strp_dot));
    `checks($typename(strp_quote), "class $unit::StrP#(\"a\\\"b\")");
    `checks($typename(strp_ctrl), "class $unit::StrP#(\"t\\tn\\n\")");
    `checks($typename(str2_ab), "class $unit::Str2#(\"a\\\",\\\"b\",\"c\")");
    `checks($typename(str2_bc), "class $unit::Str2#(\"a\",\"b\\\",\\\"c\")");
    // Of classes within each specialization of a module or interface
    `checks(mc4.mc_typename(), "class mcls#(4).MC");
    `checks(mc16.mc_typename(), "class mcls#(16).MC");
    `checks(ci4.ic_typename(), "class cifc#(4).IC");
    `checks(ci16.ic_typename(), "class cifc#(16).IC");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
