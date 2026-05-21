// DESCRIPTION: Verilator: Test that conflicting per-bit pull directions on
// the same bit of a bus produce an UNSUPPORTED error.
//
// SPDX-FileCopyrightText: 2026 Lucas Amaral
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off PINMISSING

module pullup_leaf(output wire o);
  pullup pu (o);
endmodule

module pulldown_leaf(output wire o);
  pulldown pd (o);
endmodule

module t(output wire [3:0] bus);
  // Bit 2 of 'bus' is driven by both a pullup AND a pulldown through hierarchy,
  // which is an electrical short. Verilator must reject this at compile time.
  pullup_leaf   pu_inst (.o(bus[2]));
  pulldown_leaf pd_inst (.o(bus[2]));
endmodule
