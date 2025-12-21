// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface b_if #(
    parameter p
);
  int x = p;
endinterface

module t;
  m #(.p(2)) m_i ();

  initial begin
    virtual b_if #(2) vif = m_i.b;
    int y = m_i.b.x;

    if (vif.x != 2) $stop;
    if (y != 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module m #(
    parameter p = 1
) ();
  b_if #(p) b ();
endmodule
