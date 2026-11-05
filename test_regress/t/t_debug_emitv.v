// DESCRIPTION: Verilator: Dotted reference that uses another dotted reference
// as the select expression
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

package Pkg;
  localparam PKG_PARAM = 1;

  typedef enum int {
    FOO = 0,
    BAR,
    BAZ
  } enum_t;

endpackage
package PkgImp;
  import Pkg::*;
  export Pkg::*;
endpackage

class Cls;
  bit cg_clk;
  int member = 1;
  local int lmember;
  protected int pmember;
  rand int rmember1;
  rand int rmember2;
  randc bit [1:0] rcmember;
  rand int rarray[3];
  constraint array_values {
    solve rarray[0] before rmember1;
    foreach (rarray[i]) rarray[i] == rmember1 + i;
  }
  covergroup cg_in_class @(posedge cg_clk);
    cp_m: coverpoint member {
      bins one = {1};
      bins two = {2};
    }
  endgroup
  covergroup cg_ref(ref int value);
    cp_ref: coverpoint value;
  endgroup
  function new;
    cg_in_class = new;
  endfunction
  function void method;
    if (this != this) $stop;
  endfunction
  task delay_method;
    #1;
  endtask
  task delay_caller;
    delay_method();
  endtask
endclass

class ClsParam #(type T = int, int P = 1);
  T pval;
  T tq[$];  // Queue post pass descends into the element, so T is reached with m_arrayPost
  localparam int PP = P;
endclass

class ClsParam2 #(
    type T1,
    type T2 = bit,
    parameter P3 = 3,
    parameter int P4 = 4
);
  localparam type LT = int;
  T1 a;
  T2 b;
  LT c;
  localparam int SUM = P3 + P4;
endclass

virtual class VBase;
  pure virtual function int vfunc();
endclass

class VDer extends VBase;
  function int vfunc();
    return 1;
  endfunction
endclass

class ClsExt extends Cls;
  function int inherited();
    return rmember1 + member;
  endfunction
endclass

function int rand_restricted(Cls obj, int member);
  return obj.randomize() with (rmember1, rmember2) { rmember1 < member; rmember2 < member; };
endfunction

interface Iface (
   input clk
);
  logic ifsig;
  modport mp(input ifsig);
endinterface

module t (/*AUTOARG*/
  // Inputs
  clk, in
  );
  input clk;
  input in;

  // verilator lint_off UNPACKED

  typedef enum [2:0] {
            ZERO,
            ONE = 1
  } e_t;

  typedef struct packed {
    e_t a;
  } ps_t;
  typedef struct {
    logic signed [2:0] a;
    rand logic [1:0] b;
  } us_t;
  typedef union {
    logic a;
  } union_t;

  const ps_t ps[3];
  const int c_scalar = 5;
  us_t us;
  union_t unu;

  // Signedness differing from the keyword's default
  int unsigned uns_int;

  // Ascending packed range: the declared direction must survive
  /* verilator lint_off ASCRANGE */
  logic [2:3] ascending_packed;
  /* verilator lint_on ASCRANGE */

  // Typedef of a queue: the dimension belongs after the typedef's name
  typedef int queue_t[$];
  queue_t queue_of_t;

  // Unpacked struct with an unpacked array member
  typedef struct {
    logic [3:0] marr[2];
  } usarr_t;
  usarr_t usarr;

  // Reference to a named enum, so the dtype is emitted by name rather than re-expanded
  e_t plain_enum;

  /* verilator lint_off ENUMVALUE */
  // No item has this value, so the lookup runs off the end and prints the number
  localparam e_t LP_ENUM_ODD = e_t'(7);
  // Pre-width this is a bare Const while ONE has no value yet, so the item's
  // value can be missing during the lookup
  localparam e_t LP_ENUM_ONE = 1;
  /* verilator lint_on ENUMVALUE */

  // Real to integral; its own variable, as 'i1' is written elsewhere
  int r2i;

  // Implicit type with explicit signedness
  wire signed [3:0] implicit_signed = 4'sb1;

  // Class references: a handle array, a specialization
  Cls cls_arr[3];
  ClsExt cls_ext;
  ClsParam #(bit, 2) cls_param;
  ClsParam2 #(byte, bit, 1, 2) cls_param2;
  VDer vder;

  integer i1;
  int array[3];
  initial array = '{1,2,3};
  logic [63:32] downto_32 = '0;

  function automatic int ident(int value);
     return value;
  endfunction

  Iface the_ifaces [3:0] (.*);
  localparam int CP_SCOPE_PARAM = ClsParam#(bit, 2)::PP;

  initial begin
    if ($test$plusargs("HELLO")) $display("Hello argument found.");
    if (Pkg::FOO == 0) $write("");
    if (ZERO == 0) $write("");
    $display("%p", e_t'(in));
    if ($value$plusargs("TEST=%d", i1))
      $display("value was %d", i1);
    else
      $display("+TEST= not found");
    if (downto_32[33]) $write("");
    if (downto_32[ident(33)]) $write("");
    if (|downto_32[48:40]) $write("");
    if (|downto_32[55+:3]) $write("");
    if (|downto_32[60-:7]) $write("");
    if (the_ifaces[2].ifsig) $write("");
    #1 $write("After #1 delay");
    wait(clk == 1) $write("After wait(clk == 1)");
  end

  bit [6:5][4:3][2:1] arraymanyd[10:11][12:13][14:15];

  reg [15:0] pubflat /*verilator public_flat_rw @(posedge clk) */;

  reg [15:0] pubflat_r;
  wire [15:0] pubflat_w = pubflat;

  // Variable part-select whose base is no longer a VarRef at late stages
  logic [15:0] concat_src;
  assign concat_src = {pubflat_r[7:0], pubflat_w[15:8]};
  logic [3:0] sel_idx;
  wire [1:0] var_part = concat_src[sel_idx +: 2];

  // A tri-type net, for verilogKwd's isTristate() form
  tri [1:0] tri_sig;
  assign tri_sig = in ? 2'b01 : 2'bz;
  int fd;
  int i;

  int q[$];
  int qb[$ : 3];
  int assoc[string];
  int assocassoc[string][real];
  int dyn[];

  typedef struct packed {
    logic nn1;
  } nested_named_t;
  typedef struct packed {
    struct packed {
      logic nn2;
    } nested_anonymous;
    nested_named_t nested_named;
    logic [11:10] nn3;
  } nibble_t;
  nibble_t [5:4] nibblearray[3:2];
  logic after_struct_packed;

  task t;
    $display("stmt");
  endtask
  function int f(input int v);
    $display("stmt");
    return v == 0 ? 99 : ~v + 1;
  endfunction
  function automatic void refports(ref int rq[$], ref int ra[string], ref int rd[],
                                   input int withdef = 5);
    rq.push_back(withdef);
    ra["k"] = 1;
    rd = new[1];
  endfunction

  // Implicit port type with explicit signedness
  function automatic int implicit_ports(input signed [3:0] sa);
    return int'(sa);
  endfunction
  function automatic logic signed [7:0] signed_val();
    return -1;
  endfunction
  import "DPI-C" pure function int dpi_pure(input int a);
  import "DPI-C" context function int dpi_ctx(input int a);
  import "DPI-C" dpi_c_name = function int dpi_renamed(input int a);
  import "DPI-C" task dpi_task_i(input int a);
  import "DPI-C" function int dpi_two(input int a, input int b);
  import "DPI-C" function int dpi_def(input int a = 7);
  export "DPI-C" function dpi_exported;
  function int dpi_exported(input int a);
    return a + 1;
  endfunction
  export "DPI-C" task dpi_exported_task;
  task dpi_exported_task(input int a);
    $display("exported task %0d", a);
  endtask
  import "DPI-C" function void dpii_open(input bit [] h[]);

  sub sub(.*);
  seq_event seq_event(.*);

  logic [2:0] pm_out;
  param_mod #(.PT(byte), .PW(3)) pm (
      .pin(8'sd1),
      .pout(pm_out)
  );

  initial begin
    int other;
    begin //unnamed
      for (int i = 0; i < 3; ++i) begin
        other = f(i);
        $display("stmt %d %d", i, other);
        t();
      end
    end
    begin : named
      $display("stmt");
    end : named
  end
  final begin
    $display("stmt");
  end

  always @ (in) begin
    $display("stmt");
  end
  always @ (posedge clk) begin
    $display("posedge clk");
    pubflat_r <= pubflat_w;
  end
  always @ (negedge clk) begin
    $display("negedge clk, pfr = %x", pubflat_r);
  end

  int cyc;
  int fo;
  int sum;
  real r;
  string str;
  int mod_val;
  int mod_res;
  always_ff @ (posedge clk) begin
    cyc <= cyc + 1;
    r <= r + 0.01;
    fo = cyc;
    sub.inc(fo, sum);
    sum = sub.f(sum);
    $display("[%0t] sum = %d", $time, sum);
    $display("a?= %d", $c(1) ? $c32(20) : $c32(30));

    $c(";");
    $display("%d", $c("0"));
    fd = $fopen("/dev/null");
    $fclose(fd);
    fd = $fopen("/dev/null", "r");
    $fgetc(fd);  //  stmt
    $fflush(fd);
    $fscanf(fd, "%d", sum);
    $fdisplay("i = ", sum);
    $fwrite(fd, "hello");
    $readmemh(fd, array);
    $readmemh(fd, array, 0);
    $readmemh(fd, array, 0, 0);

    sum = 0;
    for (int i = 0; i < cyc; ++i) begin
      sum += i;
      if (sum > 10) break;
      else sum += 1;
    end
    if (cyc == 99) $finish;
    if (cyc == 100) $stop;

    case (in)  // synopsys full_case parallel_case
      1: $display("1");
      default: $display("default");
    endcase
    priority case (in)
      1: $display("1");
      default: $display("default");
    endcase
    unique case (in)
      1: $display("1");
      default: $display("default");
    endcase
    unique0 case (in)
      1: $display("1");
      default: $display("default");
    endcase
    if (in) $display("1"); else $display("0");
    priority if (in) $display("1"); else $display("0");
    unique if (in) $display("1"); else $display("0");
    unique0 if (in) $display("1"); else $display("0");

    $display($past(cyc), $past(cyc, 1));

    str = $sformatf("cyc=%d", cyc);
    $display("str = %s", str);
    $display("struct = %p", ps);
    $display("%% [%t] [%t] to=%o td=%d", $time, $realtime, $time, $time);
    $sscanf("foo=5", "foo=%d", i);
    $printtimescale;
    if (i != 5) $stop;

    sum = $random;
    sum = $random(10);
    sum = $urandom;
    sum = $urandom(10);

    sum = array.sum with (item * 2);

    if (Pkg::PKG_PARAM != 1) $stop;
    sub.r = 62.0;
    `checkd(sub.sub_gen.SUB_B, 2'd1);

    mod_res = mod_val % 5;

    if (str.len() > 0) $write("");  // AstLenN
    sum = f(.v(1));  // Named argument
    r2i = int'(r);  // Real to integral: rounds
    if (r2i != 0) $write("");
    refports(q, assoc, dyn);
    sum = dpi_pure(1) + dpi_ctx(2) + dpi_renamed(3);
    sum = dpi_two(1, 2) + dpi_def();
    dpi_task_i(4);
    dpi_exported_task(5);
    if (plain_enum == LP_ENUM_ODD || plain_enum == LP_ENUM_ONE) $write("");
    if (pm_out != 0) $write("");
    // Selects by the kind of their base node, as visit(AstSel*) switches on it:
    //   VarRef    - ascending_packed[2]
    //   VarXRef   - sub.xr_vec[1]              (cross-module)
    //   MemberSel - cls_ext.member[1]          (class member)
    //   StructSel - us.a[1]                    (unpacked struct member)
    //   ArraySel  - arraymanyd[10][12][14][6]  (unpacked element, then packed)
    //   Sel       - arraymanyd[...][6][4][2]   (select of a select)
    if (us.a[1]) $write("");
    if (c_scalar != 5) $stop;
    if (sub.xr_vec[1]) $write("");
    if (cls_ext != null && cls_ext.member[1]) $write("");
    sum = implicit_ports(-4'sd1);
    if (implicit_signed < 0) $write("");
    if (cls_ext != null && cls_ext.inherited() != 0) $write("");
    if (cls_param2 != null && cls_param2.SUM != 0) $write("");
    sum = dpi_exported(3);
    if (cls_arr[0] == null) $write("");
    if (cls_param.PP != 2) $write("");
    if (vder.vfunc() != 1) $write("");
    if (after_struct_packed) $write("");
    if (ascending_packed[2]) $write("");
    if (uns_int > 0) $write("");
    if (usarr.marr[0] != 0) $write("");
    if (arraymanyd[10][12][14][6][4][2]) $write("");
    if (var_part != 0) $write("");
    if (tri_sig[0]) $write("");
    if (cls_param.tq.size() != 0) $write("");
    if (CP_SCOPE_PARAM != 2) $write("");
    sel_idx <= cyc[3:0];
    queue_of_t.push_back(1);

    $display("%g", $log10(r));
    $display("%g", $ln(r));
    $display("%g", $exp(r));
    $display("%g", $sqrt(r));
    $display("%g", $floor(r));
    $display("%g", $ceil(r));
    $display("%g", $sin(r));
    $display("%g", $cos(r));
    $display("%g", $tan(r));
    $display("%g", $asin(r));
    $display("%g", $acos(r));
    $display("%g", $atan(r));
    $display("%g", $sinh(r));
    $display("%g", $cosh(r));
    $display("%g", $tanh(r));
    $display("%g", $asinh(r));
    $display("%g", $acosh(r));
    $display("%g", $atanh(r));

    if ($sampled(cyc[1])) $write("");
    if ($rose(cyc)) $write("");
    if ($fell(cyc)) $write("");
    if ($stable(cyc)) $write("");
    if ($changed(cyc)) $write("");
    if ($past(cyc[1])) $write("");

    if ($rose(cyc, clk)) $write("");
    if ($fell(cyc, clk)) $write("");
    if ($stable(cyc, clk)) $write("");
    if ($changed(cyc, clk)) $write("");
    if ($past(cyc[1], 5)) $write("");
    if (signed_val()[3:0] != 4'hf) $stop;
    force sum = 10;
    repeat (2) if (sum != 10) $stop;
    release sum;
  end

  // verilog_format: off  // verible does not support clocking events inside sequence declarations
  sequence s_clocked;
    @(posedge clk) in
  endsequence
  // verilog_format: on

  assert_seq_clocked: assert property (s_clocked);

  property p;
    @(posedge clk) ##1 sum[0]
  endproperty
  property p1;
    @(clk) sum[0]
  endproperty

  assert property (@(clk) not ##1 in);

  initial begin
    assert_simple_immediate_else: assert(0) else $display("fail");
    assert_simple_immediate_stmt: assert(0) $display("pass");
    assert_simple_immediate_stmt_else: assert(0) $display("pass"); else $display("fail");

    assume_simple_immediate: assume(0);
    assume_simple_immediate_else: assume(0) else $display("fail");
    assume_simple_immediate_stmt: assume(0) $display("pass");
    assume_simple_immediate_stmt_else: assume(0) $display("pass"); else $display("fail");
  end

  assert_observed_deferred_immediate: assert #0 (0);
  assert_observed_deferred_immediate_else: assert #0 (0) else $display("fail");
  assert_observed_deferred_immediate_stmt: assert #0 (0) $display("pass");
  assert_observed_deferred_immediate_stmt_else: assert #0 (0) $display("pass"); else $display("fail");

  assume_observed_deferred_immediate: assume #0 (0);
  assume_observed_deferred_immediate_else: assume #0 (0) else $display("fail");
  assume_observed_deferred_immediate_stmt: assume #0 (0) $display("pass");
  assume_observed_deferred_immediate_stmt_else: assume #0 (0) $display("pass"); else $display("fail");

  assert_final_deferred_immediate: assert final (0);
  assert_final_deferred_immediate_else: assert final (0) else $display("fail");
  assert_final_deferred_immediate_stmt: assert final (0) $display("pass");
  assert_final_deferred_immediate_stmt_else: assert final (0) $display("pass"); else $display("fail");

  assume_final_deferred_immediate: assume final (0);
  assume_final_deferred_immediate_else: assume final (0) else $display("fail");
  assume_final_deferred_immediate_stmt: assume final (0) $display("pass");
  assume_final_deferred_immediate_stmt_else: assume final (0) $display("pass"); else $display("fail");

  property prop();
    @(posedge clk) 0
  endproperty

  assert_concurrent: assert property (prop);
  assert_concurrent_else: assert property(prop) else $display("fail");
  assert_concurrent_stmt: assert property(prop) $display("pass");
  assert_concurrent_stmt_else: assert property(prop) $display("pass"); else $display("fail");

  assume_concurrent: assume property(prop);
  assume_concurrent_else: assume property(prop) else $display("fail");
  assume_concurrent_stmt: assume property(prop) $display("pass");
  assume_concurrent_stmt_else: assume property(prop) $display("pass"); else $display("fail");

  cover_concurrent: cover property(prop);
  cover_concurrent_stmt: cover property(prop) $display("pass");

  cover_sequence_concurrent: cover sequence (@(posedge clk) in ##1 in);

  assert_prop_always: assert property (@(posedge clk) always [0:3] in);
  assert_prop_s_always: assert property (@(posedge clk) s_always [1:2] in);
  assert_prop_overlap_impl: assert property (@(posedge clk) in |-> in);
  assert_prop_nonoverlap_impl: assert property (@(posedge clk) in |=> in);
  assert_prop_overlap_fb: assert property (@(posedge clk) in #-# in);
  assert_prop_nonoverlap_fb: assert property (@(posedge clk) in #=# in);
  assert_prop_accept_on: assert property (@(posedge clk) accept_on (in) in);
  assert_prop_reject_on: assert property (@(posedge clk) reject_on (in) in);
  assert_prop_sync_accept_on: assert property (@(posedge clk) sync_accept_on (in) in);
  assert_prop_sync_reject_on: assert property (@(posedge clk) sync_reject_on (in) in);
  assert_prop_weak: assert property (@(posedge clk) weak(in));
  cover_prop_strong: cover property (@(posedge clk) strong(in));

  int a;
  int ao;

  // verilator lint_off CASTCONST
  initial begin : assert_intrinsic
    $cast(ao, a);
  end

  restrict property (@(posedge clk) ##1 a[0]);

  // Covergroup constructs - exercise AstCovergroup, AstCoverpoint, AstCoverBin, AstCoverCross
  logic [2:0] cg_sig;
  logic [1:0] cg_sig2;

  // Basic covergroup: value bins, default bin, ignore_bins, illegal_bins, options
  covergroup cg_basic;
    option.per_instance = 1;
    option.weight = 2;
    type_option.weight = 3;
    cp_sig: coverpoint cg_sig {
      bins low    = {[0:3]} iff (cg_sig2[0]);
      bins high   = {[4:6]};
      bins multi  = {0, 1, 2};   // multiple values in one bins (exercises EmitV range loop)
      bins sized[2] = {[0:5], 7};  // sized array of bins (exercises EmitV array size)
      wildcard bins wild[] = {3'b01?};  // wildcard array of bins (exercises EmitV wildcard)
      bins filtered[] = {[0:7]} with (item % 2 == 0);  // 'with' filter of a range list
      bins named = cp_sig with (item > 5);  // 'with' filter of the coverpoint's values
      bins dflt   = default;
      ignore_bins ign = {7};
      illegal_bins ill = {5};
    }
    // Coverpoint with per-coverpoint option but no explicit bins
    cp_options: coverpoint cg_sig2 {
      option.at_least = 2;
      option.weight = 4;
      type_option.weight = 5;
    }
  endgroup

  // Covergroup with clocking event
  covergroup cg_clocked @(posedge clk);
    cp_cyc: coverpoint cg_sig;
  endgroup

  // Covergroup with transition bins
  covergroup cg_trans;
    cp_t: coverpoint cg_sig {
      bins t01  = (3'b000 => 3'b001);
      bins t12  = (3'b001 => 3'b010);
      bins talt = (3'b010 => 3'b011), (3'b100 => 3'b101);  // multiple transition sets
      bins trep = (3'b000 => 3'b001 [->2]);  // repetition op -> non-NONE VTransRepType (exercises ascii())
      bins tarr[] = (3'b000 => 3'b001), (3'b001 => 3'b010);  // array transition bins -> m_isArray
    }
  endgroup

  // Covergroup with both-open and default range lists
  covergroup cg_open_default;
    open_both: coverpoint cg_sig {
      bins all[] = {[$ : $]};
    }
    defaults: coverpoint cg_sig {
      bins remaining[] = default;
    }
  endgroup

  // Covergroup with array transitions and an array-valued set expression.
  int cg_set_values[$] = '{1, 2};
  covergroup cg_forms with function sample (bit [3:0] value);
    cp: coverpoint value {
      bins lists[] = (1, 2 => 3, 4);
      ignore_bins ignored_array[] = (7 => 8);
      illegal_bins illegal_array[] = (11 => 12);
      bins selected[] = cg_set_values;
    }
  endgroup

  // Covergroup with cross coverage
  covergroup cg_cross;
    cp_x: coverpoint cg_sig {
      bins x0 = {(0)};
      bins x1 = {1};
    }
    cp_y: coverpoint cg_sig2 {
      bins y0 = {0};
      bins y1 = {1};
    }
    cx: cross cp_x, cp_y iff (cg_sig[0] == cg_sig2[0]);
    cx_select: cross cp_x, cp_y{
      option.weight = 2;
      bins entire = cx_select;
      bins plain = binsof (cp_x);
      bins named = binsof (cp_x.x0);
      bins filtered = binsof (cp_x) intersect {0, [1 : 2]};
      bins lower = binsof (cp_x) intersect {[$ : 0]};
      bins upper = binsof (cp_x) intersect {[1 : $]};
      bins negated = !binsof (cp_x.x0);
      bins complemented = !binsof (cp_x) intersect {0};
      bins either = binsof (cp_x.x0) || binsof (cp_y.y0);
      bins both = binsof (cp_x.x1) && binsof (cp_y.y1) iff (cg_sig[1]);
      bins grouped = (binsof (cp_x.x0) || binsof (cp_y.y0)) && !binsof (cp_x.x1);
      bins paired = binsof (cp_x) with (cp_x != 0 && cp_y == 0);  // 'with' filter of bin tuples
      bins counted = binsof (cp_x) with (cp_x != 0) matches 2;  // Of 2 value tuples
      bins every = cx_select with (cp_y == 0) matches $;  // Of all value tuples
      ignore_bins ignored = binsof (cp_x.x0) iff (cg_sig[0]);
      illegal_bins forbidden = binsof (cp_y.y1);
    }
  endgroup

  covergroup cg_live_cross;
    option.auto_bin_max = 4;
    cp_x: coverpoint cg_sig {
      ignore_bins removed = {0};
    }
    cp_y: coverpoint cg_sig2;
    cx: cross cp_x, cp_y{
      bins all = cx;
    }
  endgroup

  cg_basic   cg_basic_inst   = new;
  cg_clocked cg_clocked_inst = new;
  cg_trans   cg_trans_inst   = new;
  cg_cross   cg_cross_inst   = new;
  cg_live_cross cg_live_cross_inst = new;

  initial begin
    Cls obj;
    obj = new;
    obj.delay_caller();
  end
endmodule

module param_mod #(
    parameter type PT = int,
    parameter int PW = 4
) (
    input PT pin,
    output logic [PW-1:0] pout
);
  typedef PT pt_alias_t;
  pt_alias_t pt_var;
  assign pt_var = pin;
  assign pout = PW'(pt_var);
endmodule

module sub(input logic clk);
  logic [7:0] xr_vec;
  if (1) begin : sub_gen
    typedef enum logic [1:0] {SUB_A, SUB_B} sub_e;
  end
  task inc(input int i, output int o);
    o = {1'b0, i[31:1]} + 32'd1;
  endtask
  function int f(input int v);
    if (v == 0) return 33;
    return {31'd0, v[2]} + 32'd1;
  endfunction
  real r;
endmodule

module seq_event(input logic clk);
  bit a, b, c;
  sequence sq;
    @(posedge clk) a ##1 b ##1 c;
  endsequence
  initial begin
    @sq;
  end
endmodule

package p;
  logic pkgvar;
endpackage

`verilator_config
threads_group -module "sub"
