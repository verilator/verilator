// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  integer cyc = 0;
  reg [63:0] crc = 64'h5aef0c8d_d70a4497;

  wire a = crc[0];
  wire b = crc[1];
  wire c = crc[2];
  wire d = crc[3];
  wire e = crc[4];

  int f_var = 0;
  int f_ieee = 0;
  int f_collapse = 0;
  int f_over = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  default clocking @(posedge clk);
  endclocking

  // Both operands vary in length: lhs in [1,3], rhs in [2,5], common [2,3].
  // Variable-length intersect (IEEE 1800-2023 16.9.6): both match the same
  // window with equal start and end, length chosen from each operand's range.
  ap_var :
  assert property (disable iff (cyc < 2) (a & c) |-> ((a ##[1:3] b) intersect (c ##[2:5] d)))
  else f_var <= f_var + 1;

  // IEEE 16.9.6 canonical: one variable + one fixed operand, common length {4}.
  ap_ieee :
  assert property (disable iff (cyc < 2) a |-> ((a ##[1:5] b) intersect (c ##2 d ##2 e)))
  else f_ieee <= f_ieee + 1;

  // Common length collapses to {0}: (a ##[0:3] b) intersect c == a & b & c,
  // so this implication never fails (exercises the bare-boolean lowering path).
  ap_collapse :
  assert property (disable iff (cyc < 2) (a & b & c) |-> ((a ##[0:3] b) intersect c))
  else f_collapse <= f_collapse + 1;

  // Equal fixed length, one operand carrying an internal check: lowered through
  // the per-cycle conjoin, not the done-latch combiner (which conflates
  // concurrent attempts and over-accepts).
  ap_over :
  assert property (disable iff (cyc < 2) (a ##4 b) intersect (c ##2 d ##2 e))
  else f_over <= f_over + 1;

  final begin
    `checkd(f_var, 7);
    `checkd(f_ieee, 41);
    `checkd(f_collapse, 0);
    `checkd(f_over, 84);
  end
endmodule
