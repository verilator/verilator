// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Ariane-shaped 3-level hierarchy with parameter forwarding.  Each
// mid instance forwards its paramtype to its leaf.  Three distinct
// width/value tuples catch cross-hierarchy template leakage.

module leaf #(
    parameter int W = 4,
    parameter type T = logic [W-1:0],
    parameter T VAL = '0
) ();
  logic [W-1:0] observed;
  assign observed = VAL;
endmodule

module mid #(
    parameter int W = 4,
    parameter type T = logic [W-1:0],
    parameter T VAL = '0
) ();
  leaf #(
      .W(W),
      .T(T),
      .VAL(VAL)
  ) l ();
endmodule

module t;
  mid #(
      .W(8),
      .VAL(8'hA5)
  ) m_a ();
  mid #(
      .W(16),
      .VAL(16'hBEEF)
  ) m_b ();
  mid #(
      .W(32),
      .VAL(32'hDEADBEEF)
  ) m_c ();

  initial begin
    #1;
    `checkh(m_a.l.W, 8);
    `checkh($bits(m_a.l.observed), 8);
    `checkh(m_a.l.observed, 8'hA5);

    `checkh(m_b.l.W, 16);
    `checkh($bits(m_b.l.observed), 16);
    `checkh(m_b.l.observed, 16'hBEEF);

    `checkh(m_c.l.W, 32);
    `checkh($bits(m_c.l.observed), 32);
    `checkh(m_c.l.observed, 32'hDEADBEEF);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
