// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc = 0;
  logic a = 1'b1;
  logic rst = 1'b1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) rst <= 1'b0;
  end

  // a is always 1, so there is no per-cycle safety failure. The ONLY way these
  // can fail is the strong end-of-simulation liveness obligation: attempts whose
  // [m:n] window is cut off by $finish must fail (IEEE 1800-2023 16.12.11).

  // Single-tick window s_always[1:1]: its in-window state is ONE registered
  // vertex, so a dropped end-of-trace obligation produces total silence (no
  // shallower attempt can mask it). It is the most sensitive guard and shares
  // the in-window marking with every s_always[m:n], so if it fires the deeper
  // windows do too. $finish halts on the first liveness $error, so a single
  // strong assertion keeps the failure attributable to this case.
  as_mm: assert property (@(posedge clk) disable iff (rst) s_always [1:1] a);

  // Weak twin imposes no end-of-trace obligation: never fails on this trace.
  as_weak: assert property (@(posedge clk) disable iff (rst) always [1:4] a);

  always @(posedge clk) begin
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
