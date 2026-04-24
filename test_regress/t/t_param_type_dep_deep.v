// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Deep value-param chain under a type param.  Each intermediate must
// recompute per spec; template poisoning at any level fails a specific
// assertion pointing at the leaking level.  Each instance overrides
// .val (paramtype-typed) with a spec-matched width so cellPinCleanup
// processes a RefDType pin and the full W1->W2->W3->W4 chain must
// unwind.

module m #(
    parameter int  W1  = 4,
    parameter int  W2  = W1 + 4,
    parameter int  W3  = W2 * 2,
    parameter int  W4  = W3 + 1,
    parameter type T   = logic [W4-1:0],
    parameter T    val = '0
) ();
endmodule

module t;
  m #(.W1(8),  .val(25'h1234567))  iw8  ();  // W4 = 25
  m            iwd ();                       // default W4 = 17
  m #(.W1(16), .val(41'h123456789AB)) iw16 ();  // W4 = 41

  initial begin
    if (iw8.W1 !== 8)  begin $write("%%Error iw8.W1=%0d\n",  iw8.W1);  $stop; end
    if (iw8.W2 !== 12) begin $write("%%Error iw8.W2=%0d\n",  iw8.W2);  $stop; end
    if (iw8.W3 !== 24) begin $write("%%Error iw8.W3=%0d\n",  iw8.W3);  $stop; end
    if (iw8.W4 !== 25) begin $write("%%Error iw8.W4=%0d\n",  iw8.W4);  $stop; end
    if ($bits(iw8.val) !== 25) begin
      $write("%%Error $bits(iw8.val)=%0d\n", $bits(iw8.val)); $stop;
    end
    if (iw8.val !== 25'h1234567) begin $write("%%Error iw8.val=%h\n", iw8.val); $stop; end

    if (iwd.W1 !== 4)  begin $write("%%Error iwd.W1=%0d\n",  iwd.W1);  $stop; end
    if (iwd.W2 !== 8)  begin $write("%%Error iwd.W2=%0d\n",  iwd.W2);  $stop; end
    if (iwd.W3 !== 16) begin $write("%%Error iwd.W3=%0d\n",  iwd.W3);  $stop; end
    if (iwd.W4 !== 17) begin $write("%%Error iwd.W4=%0d\n",  iwd.W4);  $stop; end
    if ($bits(iwd.val) !== 17) begin
      $write("%%Error $bits(iwd.val)=%0d\n", $bits(iwd.val)); $stop;
    end

    if (iw16.W1 !== 16) begin $write("%%Error iw16.W1=%0d\n", iw16.W1); $stop; end
    if (iw16.W2 !== 20) begin $write("%%Error iw16.W2=%0d\n", iw16.W2); $stop; end
    if (iw16.W3 !== 40) begin $write("%%Error iw16.W3=%0d\n", iw16.W3); $stop; end
    if (iw16.W4 !== 41) begin $write("%%Error iw16.W4=%0d\n", iw16.W4); $stop; end
    if ($bits(iw16.val) !== 41) begin
      $write("%%Error $bits(iw16.val)=%0d\n", $bits(iw16.val)); $stop;
    end
    if (iw16.val !== 41'h123456789AB) begin
      $write("%%Error iw16.val=%h\n", iw16.val); $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
