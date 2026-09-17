// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Interleaved specs (A B A C B A).  Any cross-instance leakage from
// template poisoning causes a later instance of a repeated tuple to
// mismatch its expected value.

module m #(
    parameter int W = 8,
    parameter type T = logic [W-1:0],
    parameter T VAL = '0
) ();
  logic [W-1:0] observed;
  assign observed = VAL;
endmodule

module t;
  m #(
      .W(8),
      .VAL(8'h11)
  ) ia1 ();  // A
  m #(
      .W(16),
      .VAL(16'h2222)
  ) ib1 ();  // B
  m #(
      .W(8),
      .VAL(8'h11)
  ) ia2 ();  // A
  m #(
      .W(32),
      .VAL(32'h33333333)
  ) ic1 ();  // C
  m #(
      .W(16),
      .VAL(16'h2222)
  ) ib2 ();  // B
  m #(
      .W(8),
      .VAL(8'h11)
  ) ia3 ();  // A

  initial begin
    #1;
    `checkh($bits(ia1.observed), 8);
    `checkh($bits(ib1.observed), 16);
    `checkh($bits(ia2.observed), 8);
    `checkh($bits(ic1.observed), 32);
    `checkh($bits(ib2.observed), 16);
    `checkh($bits(ia3.observed), 8);

    `checkh(ia1.observed, 8'h11);
    `checkh(ib1.observed, 16'h2222);
    `checkh(ia2.observed, 8'h11);
    `checkh(ic1.observed, 32'h33333333);
    `checkh(ib2.observed, 16'h2222);
    `checkh(ia3.observed, 8'h11);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
