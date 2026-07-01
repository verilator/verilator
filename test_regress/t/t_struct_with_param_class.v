// DESCRIPTION: Verilator: Verilog Test module
//
// References to a parameterized-class typedef (r#(N)::t) buried inside
// unit-scope struct/union typedefs, passed as interface type-parameter
// values. Exercises resolveParamClassRefDType's recursion into
// NodeUOrStructDType members across several container shapes and a
// non-default parameter value.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class r #(parameter int W = 1);
  typedef struct packed { logic [W-1:0] unused; } t;
endclass

// Plain struct member, default param
typedef struct packed { r#(1)::t f; } tf_struct;

// Union member, default param
typedef union packed { r#(1)::t a; logic [0:0] b; } tf_union;

// Non-default param value (forces class r to be specialized, not reused)
typedef struct packed { r#(7)::t f; } tf_nondefault;

// Reference two levels deep, exercising the self-recursion
typedef struct packed {
  struct packed { r#(1)::t f; } inner;
} tf_nested;

interface ifc #(parameter type T = logic);
endinterface

module t;
  ifc #(.T(tf_struct))     bad_struct     ();
  ifc #(.T(tf_union))      bad_union      ();
  ifc #(.T(tf_nondefault)) bad_nondefault ();
  ifc #(.T(tf_nested))     bad_nested     ();

  initial begin
    tf_struct     v_struct;
    tf_union      v_union;
    tf_nondefault v_nondefault;
    tf_nested     v_nested;

    // Widths follow the specialized class parameter
    `checkh($bits(tf_struct), 32'd1);
    `checkh($bits(tf_union), 32'd1);
    `checkh($bits(tf_nondefault), 32'd7);
    `checkh($bits(tf_nested), 32'd1);

    // Write/read through the buried r#(N)::t member to make sure
    // the resolved type behaves as a real packed value
    v_struct.f.unused = 1'b1;
    `checkh(v_struct.f.unused, 1'b1);

    v_nondefault.f.unused = 7'h5a;
    `checkh(v_nondefault.f.unused, 7'h5a);

    v_nested.inner.f.unused = 1'b1;
    `checkh(v_nested.inner.f.unused, 1'b1);

    v_union.a.unused = 1'b1;
    `checkh(v_union.b, 1'b1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
