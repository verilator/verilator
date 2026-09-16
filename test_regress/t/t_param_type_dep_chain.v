// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Chained paramtypes: type B = A where A = logic[W-1:0].  The iterative
// RefDType substitution in cellPinCleanup must unwind the chain over
// multiple passes: B -> REFDTYPE(A) -> A's body -> VARREF(W) -> override.
// Each instance overrides .val (paramtype-typed, spec-matched width) so
// cellPinCleanup processes a RefDType pin that must be resolved per-spec.
// Pre-fix, pin values are checked against the template's B (8 bits),
// producing WIDTHTRUNC warnings on i16/i32.  Post-fix, they check
// against each spec's resolved B and pass cleanly.

module m #(
    parameter int W = 8,
    parameter type A = logic [W-1:0],
    parameter type B = A,
    parameter B val = '0
) ();
  A a_sig;
  B b_sig;
  initial a_sig = '1;
  initial b_sig = '1;
endmodule

module t;
  m #(
      .W(8),
      .val(8'hA5)
  ) i8 ();
  m #(
      .W(16),
      .val(16'hBEEF)
  ) i16 ();
  m #(
      .W(32),
      .val(32'hDEADBEEF)
  ) i32 ();

  initial begin
    #1;
    `checkh($bits(i8.val), 8);
    `checkh($bits(i8.a_sig), 8);
    `checkh($bits(i8.b_sig), 8);
    `checkh(i8.val, 8'hA5);
    `checkh(i8.a_sig, 8'hFF);
    `checkh(i8.b_sig, 8'hFF);

    `checkh($bits(i16.val), 16);
    `checkh($bits(i16.a_sig), 16);
    `checkh($bits(i16.b_sig), 16);
    `checkh(i16.val, 16'hBEEF);
    `checkh(i16.a_sig, 16'hFFFF);
    `checkh(i16.b_sig, 16'hFFFF);

    `checkh($bits(i32.val), 32);
    `checkh($bits(i32.a_sig), 32);
    `checkh($bits(i32.b_sig), 32);
    `checkh(i32.val, 32'hDEADBEEF);
    `checkh(i32.a_sig, 32'hFFFFFFFF);
    `checkh(i32.b_sig, 32'hFFFFFFFF);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
