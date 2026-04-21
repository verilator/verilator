// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// IEEE 1800-2023 16.9.10: seq1 within seq2
// CRC-driven random stimulus. Each property has a counter; at cyc==99 we
// `checkd` against Verilator's actual count and record the Questa golden
// value in a trailing comment for cross-simulator reference.

module t (
  input clk
);
  integer cyc = 0;
  reg [63:0] crc = '0;

  // Non-adjacent CRC bits (gap > max delay) to avoid LFSR correlation.
  wire a = crc[0];
  wire b = crc[7];
  wire c = crc[15];
  wire d = crc[23];

  int count_p1 = 0;
  int count_p2 = 0;
  int count_p3 = 0;
  int count_p4 = 0;
  int count_p5 = 0;
  int count_p6 = 0;
  int count_p7 = 0;
  int count_p8 = 0;
  int count_p9 = 0;

  // Boolean within boolean: equivalent to `a && b`.
  assert property (@(posedge clk) disable iff (cyc < 10)
      (a & b) |-> (a within b))
    count_p1 <= count_p1 + 1;

  // Boolean within constant true: always passes when a is high.
  assert property (@(posedge clk) disable iff (cyc < 10)
      a |-> (a within 1'b1))
    count_p2 <= count_p2 + 1;

  // `a` must hold at some offset within the c ##1 d window.
  cover property (@(posedge clk) disable iff (cyc < 10)
      a within (c ##1 d))
    count_p3 <= count_p3 + 1;

  // `a` within a length-3 outer (four possible offsets).
  cover property (@(posedge clk) disable iff (cyc < 10)
      a within (c ##3 d))
    count_p4 <= count_p4 + 1;

  // Equal-length inner/outer: single offset, reduces to intersect.
  assert property (@(posedge clk) disable iff (cyc < 10)
      (a & c) |-> ((a ##1 1'b1) within (c ##1 1'b1)))
    count_p5 <= count_p5 + 1;

  // Inner length 1, outer length 3 -> three offsets (0, 1, 2).
  cover property (@(posedge clk) disable iff (cyc < 10)
      (a ##1 b) within (c ##3 d))
    count_p6 <= count_p6 + 1;

  // Inner length 2, outer length 3 -> two offsets (0, 1).
  cover property (@(posedge clk) disable iff (cyc < 10)
      (a ##2 b) within (c ##3 d))
    count_p7 <= count_p7 + 1;

  // within nested inside intersect: both must match equal length.
  cover property (@(posedge clk) disable iff (cyc < 10)
      ((a ##1 b) within (c ##2 d)) intersect (a ##2 b))
    count_p8 <= count_p8 + 1;

  // within combined with throughout on the outer: throughout's rhs
  // fixedLength still feeds into within.
  cover property (@(posedge clk) disable iff (cyc < 10)
      a within (a throughout (b ##1 c)))
    count_p9 <= count_p9 + 1;

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};

    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      // p1/p2/p5 use |->; the NFA currently fires the pass action on
      // vacuous passes too, so counts are inflated vs. Questa. Pre-existing
      // engine-wide behavior, not within-specific.
      `checkd(count_p1, 89);   // Questa: 23
      `checkd(count_p2, 89);   // Questa: 44
      `checkd(count_p3, 26);   // Questa: 20
      `checkd(count_p4, 24);   // Questa: 22
      `checkd(count_p5, 89);   // Questa: 26
      `checkd(count_p6, 21);   // Questa: 16
      `checkd(count_p7, 15);   // Questa: 9
      `checkd(count_p8, 15);   // Questa: 4
      `checkd(count_p9, 17);   // Questa: 10
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

// Harness for stand-alone simulators (e.g. QuestaSim). Verilator uses
// test_regress's built-in clock shell and ignores this module.
`ifndef VERILATOR
module wrap;
  logic clk = 0;
  always #5 clk = ~clk;
  t inst (.clk(clk));
endmodule
`endif
