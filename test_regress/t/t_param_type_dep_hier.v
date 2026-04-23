// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Ariane-shaped 3-level hierarchy with parameter forwarding.  Each
// mid instance forwards its paramtype to its leaf.  Three distinct
// width/value tuples catch cross-hierarchy template leakage.

module leaf #(
    parameter int  W   = 4,
    parameter type T   = logic [W-1:0],
    parameter T    VAL = '0
) ();
  logic [W-1:0] observed;
  assign observed = VAL;
endmodule

module mid #(
    parameter int  W   = 4,
    parameter type T   = logic [W-1:0],
    parameter T    VAL = '0
) ();
  leaf #(.W(W), .T(T), .VAL(VAL)) l ();
endmodule

module t;
  mid #(.W(8),  .VAL(8'hA5))        m_a ();
  mid #(.W(16), .VAL(16'hBEEF))     m_b ();
  mid #(.W(32), .VAL(32'hDEADBEEF)) m_c ();

  initial begin
    #1;
    if (m_a.l.W !== 8) begin $write("%%Error m_a.l.W=%0d\n", m_a.l.W); $stop; end
    if ($bits(m_a.l.observed) !== 8) begin
      $write("%%Error $bits(m_a.l.observed)=%0d\n", $bits(m_a.l.observed)); $stop;
    end
    if (m_a.l.observed !== 8'hA5) begin
      $write("%%Error m_a.l.observed=%h\n", m_a.l.observed); $stop;
    end

    if (m_b.l.W !== 16) begin $write("%%Error m_b.l.W=%0d\n", m_b.l.W); $stop; end
    if ($bits(m_b.l.observed) !== 16) begin
      $write("%%Error $bits(m_b.l.observed)=%0d\n", $bits(m_b.l.observed)); $stop;
    end
    if (m_b.l.observed !== 16'hBEEF) begin
      $write("%%Error m_b.l.observed=%h\n", m_b.l.observed); $stop;
    end

    if (m_c.l.W !== 32) begin $write("%%Error m_c.l.W=%0d\n", m_c.l.W); $stop; end
    if ($bits(m_c.l.observed) !== 32) begin
      $write("%%Error $bits(m_c.l.observed)=%0d\n", $bits(m_c.l.observed)); $stop;
    end
    if (m_c.l.observed !== 32'hDEADBEEF) begin
      $write("%%Error m_c.l.observed=%h\n", m_c.l.observed); $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
