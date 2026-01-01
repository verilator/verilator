// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface b_if;
  int x = 1;
endinterface

module t;
  bind m b_if if_bind ();
  m #(.p(2)) m_i ();

  typedef virtual b_if vif_t;
  initial begin
    vif_t vif = t.m_i.if_bind;
    int y = t.m_i.if_bind.x;

    if (vif.x != 1) $stop;
    if (y != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module m #(
    parameter p = 1
) ();
endmodule
