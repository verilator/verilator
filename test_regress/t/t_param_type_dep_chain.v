// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Chained paramtypes: type B = A where A = logic[W-1:0].  The iterative
// RefDType substitution in cellPinCleanup must unwind the chain over
// multiple passes: B -> REFDTYPE(A) -> A's body -> VARREF(W) -> override.
// Each instance overrides .val (paramtype-typed, spec-matched width) so
// cellPinCleanup processes a RefDType pin that must be resolved per-spec.
// Pre-fix, pin values are checked against the template's B (8 bits),
// producing WIDTHTRUNC warnings on i16/i32.  Post-fix, they check
// against each spec's resolved B and pass cleanly.

module m #(
    parameter int  W   = 8,
    parameter type A   = logic [W-1:0],
    parameter type B   = A,
    parameter B    val = '0
) ();
  A a_sig;
  B b_sig;
  initial a_sig = '1;
  initial b_sig = '1;
endmodule

module t;
  m #(.W(8),  .val(8'hA5))          i8  ();
  m #(.W(16), .val(16'hBEEF))       i16 ();
  m #(.W(32), .val(32'hDEADBEEF))   i32 ();

  initial begin
    #1;
    if ($bits(i8.val) !== 8) begin
      $write("%%Error $bits(i8.val)=%0d\n", $bits(i8.val)); $stop;
    end
    if ($bits(i8.a_sig) !== 8) begin
      $write("%%Error $bits(i8.a_sig)=%0d\n", $bits(i8.a_sig)); $stop;
    end
    if ($bits(i8.b_sig) !== 8) begin
      $write("%%Error $bits(i8.b_sig)=%0d\n", $bits(i8.b_sig)); $stop;
    end
    if (i8.val !== 8'hA5)     begin $write("%%Error i8.val=%h\n",   i8.val);   $stop; end
    if (i8.a_sig !== 8'hFF)   begin $write("%%Error i8.a_sig=%h\n", i8.a_sig); $stop; end
    if (i8.b_sig !== 8'hFF)   begin $write("%%Error i8.b_sig=%h\n", i8.b_sig); $stop; end

    if ($bits(i16.val) !== 16) begin
      $write("%%Error $bits(i16.val)=%0d\n", $bits(i16.val)); $stop;
    end
    if ($bits(i16.a_sig) !== 16) begin
      $write("%%Error $bits(i16.a_sig)=%0d\n", $bits(i16.a_sig)); $stop;
    end
    if ($bits(i16.b_sig) !== 16) begin
      $write("%%Error $bits(i16.b_sig)=%0d\n", $bits(i16.b_sig)); $stop;
    end
    if (i16.val !== 16'hBEEF)    begin $write("%%Error i16.val=%h\n",   i16.val);   $stop; end
    if (i16.a_sig !== 16'hFFFF)  begin $write("%%Error i16.a_sig=%h\n", i16.a_sig); $stop; end
    if (i16.b_sig !== 16'hFFFF)  begin $write("%%Error i16.b_sig=%h\n", i16.b_sig); $stop; end

    if ($bits(i32.val) !== 32) begin
      $write("%%Error $bits(i32.val)=%0d\n", $bits(i32.val)); $stop;
    end
    if ($bits(i32.a_sig) !== 32) begin
      $write("%%Error $bits(i32.a_sig)=%0d\n", $bits(i32.a_sig)); $stop;
    end
    if ($bits(i32.b_sig) !== 32) begin
      $write("%%Error $bits(i32.b_sig)=%0d\n", $bits(i32.b_sig)); $stop;
    end
    if (i32.val !== 32'hDEADBEEF)    begin $write("%%Error i32.val=%h\n",   i32.val);   $stop; end
    if (i32.a_sig !== 32'hFFFFFFFF)  begin $write("%%Error i32.a_sig=%h\n", i32.a_sig); $stop; end
    if (i32.b_sig !== 32'hFFFFFFFF)  begin $write("%%Error i32.b_sig=%h\n", i32.b_sig); $stop; end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
