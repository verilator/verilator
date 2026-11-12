// DESCRIPTION: Verilator: Nonblocking assignments in always_latch keep their semantics
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;
  logic en_p = 0;  // Active-high latch enable
  logic en_n = 1;  // Active-low latch enable
  logic [3:0] d = 0;

  // Enables and data change on the rising clock edge
  always @(posedge clk) begin
    cyc <= cyc + 1;
    en_p <= cyc[1];
    en_n <= ~cyc[2];
    d <= d + 4'd3;
  end

  // Latches of both polarities
  logic [3:0] lp, ln;
  always_latch if (en_p) lp <= d;
  always_latch if (!en_n) ln <= d;

  // Flops sampling the latches on the edge that opens them see the previous latch value
  logic [3:0] qp, qn;
  always @(posedge en_p) qp <= lp;
  always @(negedge en_n) qn <= ln;

  // Two-phase pair: l2 is transparent while l1 is opaque
  logic [3:0] l1, l2;
  always_latch if (en_p) l1 <= d;
  always_latch if (!en_p) l2 <= l1;

  // Chain of latches transparent together: l4 follows d through l3
  logic [3:0] l3, l4;
  always_latch if (en_p) l3 <= d;
  always_latch if (en_p) l4 <= l3;

  // Reference model, evaluated when everything has settled
  logic [3:0] lp_r = 0, ln_r = 0, qp_r = 0, qn_r = 0, l1_r = 0, l2_r = 0, l4_r = 0;
  logic en_p_q = 0, en_n_q = 1;
  always @(negedge clk) begin
    if (en_p && !en_p_q) qp_r = lp_r;
    if (!en_n && en_n_q) qn_r = ln_r;
    if (en_p) lp_r = d;
    if (!en_n) ln_r = d;
    if (en_p) l1_r = d;
    if (!en_p) l2_r = l1_r;
    if (en_p) l4_r = d;
    en_p_q = en_p;
    en_n_q = en_n;
    if (cyc > 1) begin
      `checkh(lp, lp_r);
      `checkh(ln, ln_r);
      `checkh(qp, qp_r);
      `checkh(qn, qn_r);
      `checkh(l1, l1_r);
      `checkh(l2, l2_r);
      `checkh(l4, l4_r);
    end
    if (cyc == 40) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
