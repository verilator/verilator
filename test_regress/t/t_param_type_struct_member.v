// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Method/member access on a value-parameter whose type is
// the enclosing module's type-parameter.

typedef struct packed {
  logic [7:0] S_TIMER;
  logic [7:0] M_TIMER;
  logic [7:0] M_EXT;
} my_irq_t;

module leaf #(
    parameter type interrupts_t = logic,
    parameter interrupts_t INTERRUPTS = '0
) ();
  logic [7:0] observed;
  always_comb observed = INTERRUPTS.M_TIMER;
endmodule

module mid #(
    parameter type interrupts_t = logic,
    parameter interrupts_t INTERRUPTS = '0
) ();
  leaf #(
      .interrupts_t(interrupts_t),
      .INTERRUPTS(INTERRUPTS)
  ) l ();
endmodule

module t;
  localparam type irq_t = my_irq_t;
  localparam irq_t IRQ = '{S_TIMER: 8'hAA, M_TIMER: 8'h55, M_EXT: 8'hCC};
  mid #(
      .interrupts_t(irq_t),
      .INTERRUPTS(IRQ)
  ) m ();
  initial begin
    #1;
    if (m.l.observed !== 8'h55) begin
      $write("%%Error: observed=%h expected 55\n", m.l.observed);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
