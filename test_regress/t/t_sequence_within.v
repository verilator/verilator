// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
  input clk
);
  integer cyc = 0;
  reg [63:0] crc = '0;
  reg [63:0] sum = '0;

  wire a = crc[0];
  wire b = crc[1];
  wire c = crc[2];
  wire d = crc[3];

  wire [63:0] result = {60'h0, d, c, b, a};

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};

    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= '0;
    end else if (cyc < 10) begin
      sum <= '0;
    end else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkh(sum, 64'hdb7bc8bfe61f987e);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // =========================================================================
  // Boolean within (IEEE 1800-2023 16.9.10, degenerate length-1 case)
  // =========================================================================

  // Boolean within boolean: equivalent to `a && b`.
  assert property (@(posedge clk) disable iff (cyc < 2)
      (a & b) |-> (a within b));

  // Boolean within constant true: always passes when a is high.
  assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> (a within 1'b1));

  // =========================================================================
  // Boolean LHS inside multi-cycle outer (boolean within sequence)
  // =========================================================================

  // `a` must hold at some offset within the c ##1 d window.
  cover property (@(posedge clk)
      a within (c ##1 d));

  // `a` within a length-3 outer (four possible offsets).
  cover property (@(posedge clk)
      a within (c ##3 d));

  // =========================================================================
  // Multi-cycle inner within same-length outer (single offset)
  // =========================================================================

  // equal-length: one offset, reduces to intersect.
  assert property (@(posedge clk)
      (a & c) |-> ((a ##1 1'b1) within (c ##1 1'b1)));

  // =========================================================================
  // Multi-cycle inner within longer outer (multiple offsets)
  // =========================================================================

  // inner length 1, outer length 3 -> three offsets (0, 1, 2).
  cover property (@(posedge clk)
      (a ##1 b) within (c ##3 d));

  // inner length 2, outer length 3 -> two offsets (0, 1).
  cover property (@(posedge clk)
      (a ##2 b) within (c ##3 d));

  // =========================================================================
  // Combinations with other sequence operators
  // =========================================================================

  // within nested inside intersect: both must match equal length.
  cover property (@(posedge clk)
      ((a ##1 b) within (c ##2 d)) intersect (a ##2 b));

  // within nested inside within: outer within requires both operands
  // to have fixed length.
  cover property (@(posedge clk)
      (a within b) within (c ##1 d));

  // within combined with throughout on the outer: throughout's rhs
  // fixedLength still feeds into within.
  cover property (@(posedge clk)
      a within (a throughout (b ##1 c)));

endmodule
