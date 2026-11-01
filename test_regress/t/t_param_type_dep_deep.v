// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Deep value-param chain under a type param.  Each intermediate must
// recompute per spec; template poisoning at any level fails a specific
// assertion pointing at the leaking level.  Each instance overrides
// .val (paramtype-typed) with a spec-matched width so cellPinCleanup
// processes a RefDType pin and the full W1->W2->W3->W4 chain must
// unwind.

module m #(
    parameter int W1 = 4,
    parameter int W2 = W1 + 4,
    parameter int W3 = W2 * 2,
    parameter int W4 = W3 + 1,
    parameter type T = logic [W4-1:0],
    parameter T val = '0
) ();
endmodule

module t;
  m #(
      .W1(8),
      .val(25'h1234567)
  ) iw8 ();  // W4 = 25
  m iwd ();  // default W4 = 17
  m #(
      .W1(16),
      .val(41'h123456789AB)
  ) iw16 ();  // W4 = 41

  initial begin
    `checkh(iw8.W1, 8);
    `checkh(iw8.W2, 12);
    `checkh(iw8.W3, 24);
    `checkh(iw8.W4, 25);
    `checkh($bits(iw8.val), 25);
    `checkh(iw8.val, 25'h1234567);

    `checkh(iwd.W1, 4);
    `checkh(iwd.W2, 8);
    `checkh(iwd.W3, 16);
    `checkh(iwd.W4, 17);
    `checkh($bits(iwd.val), 17);

    `checkh(iw16.W1, 16);
    `checkh(iw16.W2, 20);
    `checkh(iw16.W3, 40);
    `checkh(iw16.W4, 41);
    `checkh($bits(iw16.val), 41);
    `checkh(iw16.val, 41'h123456789AB);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
