// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Original #6281 reproducer: parameter passed via localparam variable
// vs. literal constant should resolve to the same specialization.
// Fixed by ParameterizedHierBlocks::areSame fallback (landed earlier).
class ClsIntDefault #(
    parameter int P = 32
);
  function int get_p;
    return P;
  endfunction
endclass

// Parameter with byte cast default value
class ClsByteCast #(
    parameter byte P = byte'(8)
);
  function byte get_p;
    return P;
  endfunction
endclass

// Parameter with int cast default value
class ClsIntCast #(
    parameter int P = int'(42)
);
  function int get_p;
    return P;
  endfunction
endclass

// Parameter with signed cast default value
class ClsSignedCast #(
    parameter int P = int'(-5)
);
  function int get_p;
    return P;
  endfunction
endclass

// Module with cast default (cell array test)
module sub #(
    parameter byte P = byte'(8)
);
  initial begin
    `checkd(P, 8);
  end
endmodule

module t;
  // Original #6281 case: localparam variable vs. literal constant
  localparam int WIDTH = 32;
  ClsIntDefault #(32) orig_a;
  ClsIntDefault #(WIDTH) orig_b;

  // Byte cast default: #() and #(8) should be same type
  ClsByteCast #() byte_a;
  ClsByteCast #(8) byte_b;

  // Int cast default: #() and #(42) should be same type
  ClsIntCast #() int_a;
  ClsIntCast #(42) int_b;

  // Signed cast default: #() and #(-5) should be same type
  ClsSignedCast #() signed_a;
  ClsSignedCast #(-5) signed_b;

  // Multiple instances (template mutation safety)
  ClsByteCast #() multi_a;
  ClsByteCast #(8) multi_b;
  ClsByteCast #() multi_c;
  ClsByteCast #(8) multi_d;

  // Module with cast default
  sub #() sub_default ();
  sub #(8) sub_explicit ();

  initial begin
    orig_a = new;
    orig_b = orig_a;
    `checkd(orig_b.get_p(), 32);

    byte_a = new;
    byte_b = byte_a;
    `checkd(byte_a.get_p(), 8);
    `checkd(byte_b.get_p(), 8);

    int_a = new;
    int_b = int_a;
    `checkd(int_a.get_p(), 42);
    `checkd(int_b.get_p(), 42);

    signed_a = new;
    signed_b = signed_a;
    `checkd(signed_a.get_p(), -5);
    `checkd(signed_b.get_p(), -5);

    multi_a = new;
    multi_b = multi_a;
    multi_c = multi_a;
    multi_d = multi_a;
    `checkd(multi_d.get_p(), 8);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
