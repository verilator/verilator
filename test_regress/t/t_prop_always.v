// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 16.12.11 -- always / always[m:n] / s_always[m:n].
// Checks are framed to be sim-end-independent (IEEE 16.12.20 leaves weak
// vs strong end-of-sim handling to the implementation): always-true signals
// must never fail, always-false signals must always fail, and CRC-driven
// signals must actually fire at least once in both pass and fail directions.
module t (/*AUTOARG*/);

  bit clk = 0;
  always #5 clk = ~clk;

  bit [63:0] crc = 64'h5aef0c8d_d70a4497;
  int        cyc = 0;
  logic      a_rand;
  logic      a_high = 1'b1;
  logic      a_low = 1'b0;

  assign a_rand = crc[0];

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  int high_bounded_fail = 0;
  int high_sbounded_fail = 0;
  int high_degenerate_fail = 0;
  int low_bounded_pass = 0;
  int low_degenerate_pass = 0;
  int rand_bounded_pass = 0;
  int rand_bounded_fail = 0;

  // Unbounded `always P` is parse-time collapsed to P (redundant in a
  // concurrent assertion). Compile-check only.
  assert property (@(posedge clk) always 1'b1);

  // Always-true signals must NEVER trigger the else block regardless of
  // window bounds or sim-end interpretation.
  assert property (@(posedge clk) always [0:3] a_high)
  else
    high_bounded_fail++;

  assert property (@(posedge clk) s_always [1:2] a_high)
  else
    high_sbounded_fail++;

  assert property (@(posedge clk) always [0:0] a_high)
  else
    high_degenerate_fail++;

  // Always-false signals must NEVER pass.
  assert property (@(posedge clk) always [0:3] a_low)
    low_bounded_pass++;

  assert property (@(posedge clk) always [0:0] a_low)
    low_degenerate_pass++;

  // CRC-driven: must fire in both directions at least once.
  assert property (@(posedge clk) always [0:3] a_rand)
    rand_bounded_pass++;
  else
    rand_bounded_fail++;

  // Named-property wrapping compile/lint check.
  property p_always_true;
    @(posedge clk) always (1'b1);
  endproperty
  assert property (p_always_true);

  final begin
    $display("high fails: b=%0d sb=%0d deg=%0d",
             high_bounded_fail, high_sbounded_fail, high_degenerate_fail);
    $display("low passes: b=%0d deg=%0d", low_bounded_pass, low_degenerate_pass);
    $display("rand: pass=%0d fail=%0d", rand_bounded_pass, rand_bounded_fail);
    if (high_bounded_fail != 0) $fatal(1, "always[0:3] a_high failed");
    if (high_sbounded_fail != 0) $fatal(1, "s_always[1:2] a_high failed");
    if (high_degenerate_fail != 0) $fatal(1, "always[0:0] a_high failed");
    if (low_bounded_pass != 0) $fatal(1, "always[0:3] a_low passed");
    if (low_degenerate_pass != 0) $fatal(1, "always[0:0] a_low passed");
    if (rand_bounded_pass == 0) $fatal(1, "CRC bounded always never passed");
    if (rand_bounded_fail == 0) $fatal(1, "CRC bounded always never failed");
  end

endmodule
