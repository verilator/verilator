// DESCRIPTION: Verilator: Verilog Test module
//
// Typedefs and class type parameters that resolve through a
// class-scope-resolved localparam (typedef alias of a parameterized
// class, e.g. inst::b). Exercises four sub-cases:
//   - Deferred lparam used as a packed range bound in a typedef
//   - Deferred lparam used as a value argument to a parameterized class
//   - Class-scope-resolved typedef that itself depends on the param
//   - Class-scope Dot used DIRECTLY (no intermediate lparam) in a typedef
//     range inside a parameterized module, consumed by `$bits` on a child
//     cell pin
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// Sink for sub-case (4): the BITS pin consumes $bits of a typedef whose
// packed range uses class-scope Dots. V3Param must descend into the typedef's
// subDType and resolve those Dots, otherwise V3Width emits "dotted expressions
// in parameters".
module Sink #(
    parameter int BITS = 1
) ();
  logic [BITS-1:0] data;
endmodule

// Parameterized wrapper so the class specialization is deferred until V3Param
// processes the cell instance.
module Sub #(
    parameter int W = 8
) ();
  // Inner class — same shape as `t`'s C, repeated here to keep sub-case (4)
  // self-contained inside Sub.
  virtual class CInner #(
      parameter int a
  );
    localparam int b = a;
  endclass

  typedef CInner#(W) CFG;

  // (4) typedef packed range uses class-scope Dots directly
  typedef logic [(CFG::b + CFG::b - 1):0] dot_range_t;

  Sink #(.BITS($bits(dot_range_t))) u_sink ();
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

  // (4) parameterized wrapper with a typedef range using class Dots directly
  Sub #(.W(8)) u_sub ();

  initial begin
    `checkh(b8, 32'd8);
    `checkh(from_def_b, 32'd8);
    `checkh(via_bits, 32'd8);
    data_value = '1;
    `checkh(data_value, 8'hff);
    wide_bus = '1;
    `checkh(wide_bus, 8'hff);
    // sub-case (4): $bits(dot_range_t) = CFG::b + CFG::b = 8 + 8 = 16
    `checkh($bits(u_sub.u_sink.data), 32'd16);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
