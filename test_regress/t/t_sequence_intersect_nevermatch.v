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

  int f_fix = 0;
  int f_dis = 0;

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  default clocking @(posedge clk);
  endclocking

  // An intersect whose operands share no common length compiles and never
  // matches (IEEE 1800-2023 16.9.6 requires a window of equal length). Each
  // form is the antecedent of `|-> 1'b0`: it stays vacuous while it never
  // matches, so the else fires once per match -- pinned to 0. A spurious match
  // would both fail the assertion and bump the counter.

  // Unequal fixed lengths: {2} vs {3}.
  ap_fix :
  assert property (disable iff (cyc < 2) ((a ##2 b) intersect (c ##3 d)) |-> 1'b0)
  else f_fix <= f_fix + 1;

  // Disjoint ranges: {1,2} vs {4,5}.
  ap_dis :
  assert property (disable iff (cyc < 2) ((a ##[1:2] b) intersect (c ##[4:5] d)) |-> 1'b0)
  else f_dis <= f_dis + 1;

  final begin
    // TODO need better non-zero test
    `checkd(f_fix, 0);
    `checkd(f_dis, 0);
  end
endmodule
