// DESCRIPTION: Verilator: Verilog Test module
//
// Typedefs and class type parameters that resolve through a
// class-scope-resolved localparam (typedef alias of a parameterized
// class, e.g. inst::b). Exercises five sub-cases:
//   - Deferred lparam used as a packed range bound in a typedef
//   - Deferred lparam used as a value argument to a parameterized class
//   - Class-scope-resolved typedef that itself depends on the param
//   - Class-scope Dot used DIRECTLY (no intermediate lparam) in a typedef
//     range, consumed by `$bits` on a child cell pin
//   - Struct lparam field access via class-scope Dot
//     (`CFG::struct_lparam.field`) inside a parameterized module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module Sub #(parameter int W = 8) (); endmodule

// Sub-case (5): struct lparam field access via class-scope Dot.  Needs a
// parameterized-module wrapper so the class specialization is deferred until
// V3Param processes the cell instance.
typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;

class P #(parameter pair_t p);
  localparam pair_t pp = p;
endclass

module PairHolder #(parameter pair_t cfg = '{hi:'d7, lo:'d11}) ();
  typedef P#(cfg) PALIAS;
  localparam logic [7:0] hi_val = PALIAS::pp.hi;
  localparam logic [7:0] lo_val = PALIAS::pp.lo;
endmodule

module t;
  virtual class C #(
      parameter int a
  );
    localparam int b = a;
    typedef logic [a-1:0] inner_t;
    // localparam derived from a typedef inside the same class -
    // resolveDotToTypedef must constify this when reached via CFG::width.
    localparam int width = $bits(inner_t);
  endclass

  typedef C#(8) c8;

  // Deferred lparam (direct Dot)
  localparam int b8 = c8::b;

  // (1) typedef range driven by a deferred lparam
  typedef logic [b8-1:0] data_t;
  data_t data_value;

  // (2) class type-arg uses a deferred lparam value
  typedef C#(b8) c_from_def;
  localparam int from_def_b = c_from_def::b;

  // (3) class-scope-resolved typedef computed via $bits(inner_t)
  localparam int via_bits = c8::width;

  // Wire whose range comes from a deferred lparam
  logic [b8-1:0] wide_bus;

  // (4) Cell pin $bits consumes a typedef whose packed range is built from
  // class-scope Dots directly (no intermediate deferred lparam).
  typedef logic [(c8::b + c8::b - 1):0] direct_use_t;
  Sub #(.W($bits(direct_use_t))) u_sub ();

  // (5) struct lparam field access via class-scope Dot
  PairHolder #(.cfg('{hi:'d7, lo:'d11})) u_ph ();

  initial begin
    `checkh(b8, 32'd8);
    `checkh(from_def_b, 32'd8);
    `checkh(via_bits, 32'd8);
    data_value = '1;
    `checkh(data_value, 8'hff);
    wide_bus = '1;
    `checkh(wide_bus, 8'hff);
    // sub-case (4): $bits(direct_use_t) = c8::b + c8::b = 8 + 8 = 16
    `checkh($bits(direct_use_t), 32'd16);
    // sub-case (5): struct lparam field access folds to the right field
    `checkh(u_ph.hi_val, 8'd7);
    `checkh(u_ph.lo_val, 8'd11);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
