// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc;
  reg [63:0] crc;

  // CRC bits chosen far apart to keep antecedent/consequent uncorrelated.
  wire trig = crc[0];
  wire c = crc[10];
  wire d = crc[20] | crc[40];

  int fail_nonoverlap = 0;
  int fail_overlap = 0;

  // Weak non-overlapping until as implication consequent.
  // IEEE 1800-2023 16.12.12: c true at every tick until at least one tick
  // before d holds. Cycle-aggregated reject fires when c=0 and d=0 in a cycle
  // where the consequent attempt is still live.
  assert property (@(posedge clk) trig |=> c until d)
  else fail_nonoverlap = fail_nonoverlap + 1;

  // Weak overlapping (until_with) as implication consequent.
  assert property (@(posedge clk) trig |=> c until_with d)
  else fail_overlap = fail_overlap + 1;

  // Exercises buildUntil's bit-coerce branch: V3Width leaves unsized constants
  // at their nominal 32-bit dtype, so hoist-temp assignments need an explicit
  // 1-bit reduction. The assertion itself is trivially true (q == 1).
  assert property (@(posedge clk) trig |=> 0 until 1);

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x trig=%b c=%b d=%b\n", $time, cyc, crc, trig, c, d);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 99) begin
      // Counts reflect NFA per-cycle reject aggregation, not Questa's
      // per-attempt action_block firing; the two differ by a small constant
      // (see PR description for the model gap). Test is a regression for
      // "no internal error on `until` as |=> consequent" (issue #7548).
      `checkd(fail_nonoverlap, 7);
      `checkd(fail_overlap, 22);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
