// DESCRIPTION: Verilator: Dependent class type parameter
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Petr Nohavica
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Dep #(
    type E = bit,
    type M = E[2:1],
    type L = M[4:2]
);
  typedef L lane_t;
endclass

class DepValue #(
    int N = 2,
    int M = N + 1,
    type E = bit,
    type L = E[M-1:0]
);
  typedef L lane_t;
  int marker;
endclass

class AliasBox #(int N = 8);
  typedef logic [N-1:0] vec_t;
endclass

class AliasWrap #(type T = int);
  typedef struct packed {
    T a;
    T b;
  } pair_t;
endclass

class IdentityWrap #(type T = int);
  typedef T same_t;
endclass

// Cross the historical scale of fixed recursion guards while keeping the resulting value
// eight bits wide.  Every default still requires a distinct specialization and member
// projection fact, so this checks convergence depth rather than C++ wide-value support.
class DeepIdentity #(
    type I0 = byte,
    type I1 = IdentityWrap#(I0)::same_t,
    type I2 = IdentityWrap#(I1)::same_t,
    type I3 = IdentityWrap#(I2)::same_t,
    type I4 = IdentityWrap#(I3)::same_t,
    type I5 = IdentityWrap#(I4)::same_t,
    type I6 = IdentityWrap#(I5)::same_t,
    type I7 = IdentityWrap#(I6)::same_t,
    type I8 = IdentityWrap#(I7)::same_t,
    type I9 = IdentityWrap#(I8)::same_t,
    type I10 = IdentityWrap#(I9)::same_t,
    type I11 = IdentityWrap#(I10)::same_t,
    type I12 = IdentityWrap#(I11)::same_t,
    type I13 = IdentityWrap#(I12)::same_t,
    type I14 = IdentityWrap#(I13)::same_t,
    type I15 = IdentityWrap#(I14)::same_t,
    type I16 = IdentityWrap#(I15)::same_t,
    type I17 = IdentityWrap#(I16)::same_t,
    type I18 = IdentityWrap#(I17)::same_t,
    type I19 = IdentityWrap#(I18)::same_t,
    type I20 = IdentityWrap#(I19)::same_t,
    type I21 = IdentityWrap#(I20)::same_t,
    type I22 = IdentityWrap#(I21)::same_t,
    type I23 = IdentityWrap#(I22)::same_t,
    type I24 = IdentityWrap#(I23)::same_t,
    type I25 = IdentityWrap#(I24)::same_t,
    type I26 = IdentityWrap#(I25)::same_t,
    type I27 = IdentityWrap#(I26)::same_t,
    type I28 = IdentityWrap#(I27)::same_t,
    type I29 = IdentityWrap#(I28)::same_t,
    type I30 = IdentityWrap#(I29)::same_t,
    type I31 = IdentityWrap#(I30)::same_t,
    type I32 = IdentityWrap#(I31)::same_t,
    type I33 = IdentityWrap#(I32)::same_t,
    type I34 = IdentityWrap#(I33)::same_t,
    type I35 = IdentityWrap#(I34)::same_t,
    type I36 = IdentityWrap#(I35)::same_t,
    type I37 = IdentityWrap#(I36)::same_t,
    type I38 = IdentityWrap#(I37)::same_t,
    type I39 = IdentityWrap#(I38)::same_t,
    type I40 = IdentityWrap#(I39)::same_t,
    type I41 = IdentityWrap#(I40)::same_t,
    type I42 = IdentityWrap#(I41)::same_t,
    type I43 = IdentityWrap#(I42)::same_t,
    type I44 = IdentityWrap#(I43)::same_t,
    type I45 = IdentityWrap#(I44)::same_t,
    type I46 = IdentityWrap#(I45)::same_t,
    type I47 = IdentityWrap#(I46)::same_t,
    type I48 = IdentityWrap#(I47)::same_t,
    type I49 = IdentityWrap#(I48)::same_t,
    type I50 = IdentityWrap#(I49)::same_t,
    type I51 = IdentityWrap#(I50)::same_t,
    type I52 = IdentityWrap#(I51)::same_t,
    type I53 = IdentityWrap#(I52)::same_t,
    type I54 = IdentityWrap#(I53)::same_t,
    type I55 = IdentityWrap#(I54)::same_t,
    type I56 = IdentityWrap#(I55)::same_t,
    type I57 = IdentityWrap#(I56)::same_t,
    type I58 = IdentityWrap#(I57)::same_t,
    type I59 = IdentityWrap#(I58)::same_t,
    type I60 = IdentityWrap#(I59)::same_t,
    type I61 = IdentityWrap#(I60)::same_t,
    type I62 = IdentityWrap#(I61)::same_t,
    type I63 = IdentityWrap#(I62)::same_t,
    type I64 = IdentityWrap#(I63)::same_t,
    type I65 = IdentityWrap#(I64)::same_t,
    type I66 = IdentityWrap#(I65)::same_t,
    type I67 = IdentityWrap#(I66)::same_t,
    type I68 = IdentityWrap#(I67)::same_t,
    type I69 = IdentityWrap#(I68)::same_t,
    type I70 = IdentityWrap#(I69)::same_t,
    type I71 = IdentityWrap#(I70)::same_t,
    type I72 = IdentityWrap#(I71)::same_t,
    type I73 = IdentityWrap#(I72)::same_t,
    type I74 = IdentityWrap#(I73)::same_t,
    type I75 = IdentityWrap#(I74)::same_t,
    type I76 = IdentityWrap#(I75)::same_t,
    type I77 = IdentityWrap#(I76)::same_t,
    type I78 = IdentityWrap#(I77)::same_t,
    type I79 = IdentityWrap#(I78)::same_t,
    type I80 = IdentityWrap#(I79)::same_t
);
  typedef I80 result_t;
endclass

// IEEE 1800-2023 8.25.1 and Annex A data_type/class_scope permit a type parameter
// default to project a type from an explicit class specialization.  Every default
// below depends on the preceding binding and introduces another specialization and
// member projection; resolution must therefore converge without a fixed depth limit.
class DeepProjection #(
    type T0 = byte,
    type T1 = AliasWrap#(T0)::pair_t,
    type T2 = AliasWrap#(T1)::pair_t,
    type T3 = AliasWrap#(T2)::pair_t,
    type T4 = AliasWrap#(T3)::pair_t,
    type T5 = AliasWrap#(T4)::pair_t,
    type T6 = AliasWrap#(T5)::pair_t,
    type T7 = AliasWrap#(T6)::pair_t,
    type T8 = AliasWrap#(T7)::pair_t
);
  typedef T8 result_t;
endclass

class Field #(int W = 8);
  typedef struct packed {
    logic [W-1:0] value;
  } field_t;
endclass

class Stream #(type T = logic);
  T value;
endclass

class FieldPacker #(
    int InMaxW = 64,
    int OutMaxW = InMaxW
);
  typedef Field#(InMaxW) in_field_t;
  typedef Field#(OutMaxW) out_field_t;
  typedef in_field_t::field_t input_t;
  typedef out_field_t::field_t output_t;

  Stream#(input_t) in_stream;
  Stream#(output_t) out_stream;

  function new();
    in_stream = new;
    out_stream = new;
  endfunction
endclass

class AxisTypes #(
    int DATAW = 32,
    int USERW = 1
);
  localparam int KEEPW = (DATAW + 7) / 8;
  typedef struct packed {
    logic [DATAW-1:0] data;
    logic [KEEPW-1:0] keep;
    logic [USERW-1:0] user_data;
    logic             last;
  } transfer_t;
endclass

class Axis #(
    int DATAW = 32,
    int USERW = 1
);
  typedef AxisTypes#(DATAW, USERW) types_t;
  typedef types_t::transfer_t transfer_t;
  Stream#(transfer_t) stream;

  function new();
    stream = new;
  endfunction
endclass

class PositionalResult #(
    type V = int,
    type E = bit
);
  V value;

  static function PositionalResult#(V, E) create(V value);
    PositionalResult#(V, E) result = new;
    result.value = value;
    return result;
  endfunction
endclass

class MemberBase #(int V = 3);
  localparam int M = V * 2;
endclass

class MemberChain #(int V = 3);
  localparam int N = MemberBase#(V)::M + 1;
endclass

// Resolving more than one projected value in an expression must not depend on the global
// clone epoch.  Each nested projection has a distinct specialization source.
class ProjectionPair #(int UNUSED = 0);
  localparam int SUM = MemberBase#(3)::M + MemberBase#(4)::M;
endclass

class NestedActualInner #(type T = int);
  T value;
endclass

// B clones the explicit actual for A, including the nested reference's materialized defaults.
class NestedActualOuter #(
    type A = int,
    type B = A
);
  A a;
  B b;
endclass

class EmptyActual #(int U = 1, int V = 2);
  int marker;
endclass

class DepRendezvous;
endclass

class DepChannel #(type T = int) extends DepRendezvous;
  T val;
endclass

class DepTapped #(
    type T,
    type BaseT = DepChannel#(T)
) extends BaseT;
endclass

module t;
  typedef Dep#(logic [6:0])::lane_t lane7_t;
  typedef Dep#(logic [4:0])::lane_t lane5_t;
  typedef DepValue#(.N(3), .E(logic [3:0]))::lane_t value_lane_t;
  lane7_t lane7;
  lane5_t lane5;
  value_lane_t value_lane;

  // Each projection must retain which specialization its alias denotes.  Looking up pair_t in
  // the generic AliasWrap loses this distinction once both specializations exist.
  typedef AliasWrap#(int) wrap_int_t;
  typedef wrap_int_t::pair_t pair_int_t;
  typedef AliasWrap#(pair_int_t) wrap_pair_t;
  typedef wrap_pair_t::pair_t pair_pair_t;
  pair_pair_t pair_pair;

  typedef DeepProjection#()::result_t deep_result_t;
  deep_result_t deep_result;
  typedef DeepIdentity#()::result_t deep_identity_t;
  deep_identity_t deep_identity;

  // The first projection is consumed while specializing the second class, so postponing all
  // alias-member lookups until after V3Param is too late.
  typedef AliasBox#(8) box8_t;
  typedef box8_t::vec_t vec8_t;
  vec8_t vec8;
  typedef AliasWrap#(type(vec8)) wrap_vec_t;
  typedef wrap_vec_t::pair_t pair_vec_t;
  pair_vec_t pair_vec;
  // Ordinary typedef aliases are semantic edges: the outer alias has no AST child leading to
  // Field64_t::field_t, but consumers must still wait for that projection to specialize.
  typedef Field#(64) Field64_t;
  typedef Field64_t::field_t EthField_t;
  Stream#(EthField_t) eth_stream;

  // The projected member itself contains another projection.  Axis::transfer_t must wait for
  // AxisTypes::transfer_t instead of publishing the generic nested typedef.
  Axis#(80, 3) axis80;

  // These aliases first become visible inside the cloned FieldPacker specialization, after the
  // concrete Field sources may already have published.
  FieldPacker#(40, 65) field_packer;

  // Positional syntax is only a parser spelling.  Once formal identity is known, cloned
  // self-references must carry the formal names rather than __paramNumberN placeholders.
  PositionalResult#(byte, logic [3:0]) positional_result;
  typedef MemberChain#(5) MemberChain5_t;
  localparam int CHAINED_MEMBER = MemberChain5_t::N;
  DepTapped#(logic [64:0]) tapped;
  DepValue#(.N(3)) value_default;
  DepValue#(.N(3), .M(4)) value_explicit;
  DepValue#(.M(4), .N(3)) value_reordered;
  typedef ProjectionPair#() ProjectionPair_t;
  localparam int PROJECTION_SUM = ProjectionPair_t::SUM;
  NestedActualOuter#(.A(NestedActualInner#())) nested_actual;
  EmptyActual#(.V(3)) empty_actual_implicit;
  EmptyActual#(.U(), .V(3)) empty_actual_named;

  initial begin
    `checkd($bits(lane7), 42);
    `checkd($bits(lane5), 30);
    `checkd($bits(value_lane), 16);
    `checkd($bits(pair_pair), 128);
    `checkd($bits(deep_result), 2048);
    `checkd($bits(deep_identity), 8);
    `checkd($bits(pair_vec), 16);
    eth_stream = new;
    `checkd($bits(eth_stream.value), 64);
    axis80 = new;
    `checkd($bits(axis80.stream.value), 94);
    field_packer = new;
    `checkd($bits(field_packer.in_stream.value), 40);
    `checkd($bits(field_packer.out_stream.value), 65);
    positional_result = PositionalResult#(byte, logic [3:0])::create(8'h5a);
    `checkd(positional_result.value, 8'h5a);
    `checkd(CHAINED_MEMBER, 11);
    tapped = new;
    `checkd($bits(tapped.val), 65);
    value_explicit = new;
    value_explicit.marker = 17;
    // Omitting a dependent default and spelling its resolved value explicitly denote the same
    // specialization.  This assignment diagnoses divergent specialization identities.
    value_default = value_explicit;
    `checkd(value_default.marker, 17);
    value_reordered = value_default;
    `checkd(value_reordered.marker, 17);
    `checkd(PROJECTION_SUM, 14);
    nested_actual = new;
    nested_actual.a = new;
    nested_actual.a.value = 23;
    nested_actual.b = nested_actual.a;
    `checkd(nested_actual.b.value, 23);
    empty_actual_implicit = new;
    empty_actual_implicit.marker = 29;
    empty_actual_named = empty_actual_implicit;
    `checkd(empty_actual_named.marker, 29);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
