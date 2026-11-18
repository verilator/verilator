// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// The LATCHDLY repair: latches written as 'always' with an explicit
// sensitivity list keep non-blocking semantics, so a flop reading the latch
// output on the edge that opens the latch gets the old value.

module t (
    input clk
);
  int cyc;
  logic [7:0] d;
  logic [7:0] q;
  logic [7:0] s;
  logic [7:0] q_low;
  logic en_l;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    d <= d + 1;
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Clock gate, opening every other cycle
  always @(clk or cyc) if (!clk) en_l <= cyc[0];
  wire gclk = clk & en_l;

  // Latch opened by the gated clock
  always @(gclk or d) if (gclk) q <= d;

  // Flop reading the latch output on the edge that opens the latch
  always @(posedge clk) s <= q;

  // The flop must see the value the latch held before the edge
  always @(negedge clk) begin
    if (cyc > 3 && s !== q_low) begin
      $display("%%Error: cyc=%0d s=%0d expected %0d", cyc, s, q_low);
      $stop;
    end
    q_low <= q;
  end
endmodule
