// DESCRIPTION: Verilator: Nonblocking assignments in always_latch keep their semantics
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  int v;
  function new(int x);
    v = x;
  endfunction
endclass

module t (
    input clk
);
  typedef logic [64:0] w65_t;

  int cyc = 0;
  logic en_p = 0;  // Active-high latch enable
  logic en_n = 1;  // Active-low latch enable
  logic en = 0;  // Open from cycle 1 on
  logic [6:0] d = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    en_p <= cyc[1];
    en_n <= ~cyc[2];
    en <= 1;
    d <= d + 7'd3;
  end

  // Latches of both polarities, and flops on the edge that opens them, which see the previous
  // latch value
  logic [6:0] lp, ln, qp, qn;
  always_latch if (en_p) lp <= d;
  always_latch if (!en_n) ln <= d;
  always @(posedge en_p) qp <= lp;
  always @(negedge en_n) qn <= ln;

  // Two-phase pair: l2 is transparent while l1 is opaque
  logic [14:0] l1, l2;
  always_latch if (en_p) l1 <= {8'h5a, d};
  always_latch if (!en_p) l2 <= l1;

  // Chain of latches transparent together: l4 follows d through l3
  logic [6:0] l3, l4;
  always_latch if (en_p) l3 <= d;
  always_latch if (en_p) l4 <= l3;

  // Open at time zero with inputs that never change, read directly and through a wire
  logic t0_en = 1;
  logic [32:0] t0_d = 33'h1_2345_6789;
  wire [32:0] t0_w = t0_d;
  logic [32:0] t0_var, t0_wire;
  always_latch if (t0_en) t0_var <= t0_d;
  always_latch if (t0_en) t0_wire <= t0_w;

  // A flop stage and a latch stage, transparent while clk is high, in one variable: the latch
  // follows the flop output that changes just after it opens
  w65_t wide = 0;
  always @(posedge clk) wide[31:0] <= wide[31:0] + 32'h1234_5679;
  always_latch if (clk) wide[64:33] <= wide[31:0];
  logic [6:0] stages[1:2];
  logic [13:0] words[3:1];
  initial begin
    stages[1] = 0;
    words[1] = 0;
    words[3] = 0;
  end
  always @(posedge clk) begin
    stages[1] <= stages[1] + 7'd5;
    words[1][13:7] <= words[1][13:7] + 7'd3;
    words[3][13:7] <= words[3][13:7] + 7'd5;
  end
  always_latch if (clk) stages[2] <= stages[1];
  always_latch if (clk) begin
    words[1][6:0] <= words[1][13:7];
    words[3][6:0] <= words[3][13:7];
  end
  logic [31:0] qw;
  always @(posedge clk) qw <= wide[64:33];

  // Ascending packed bounds, and descending packed bounds with a nonzero low bound
  // verilator lint_off ASCRANGE
  logic [3:17] ascending = 0;
  // verilator lint_on ASCRANGE
  logic [21:7] offset = 0;
  always @(posedge clk) begin
    ascending[11:17] <= d;
    offset[13:7] <= d;
  end
  always_latch if (clk) ascending[3:9] <= ascending[11:17];
  always_latch if (clk) offset[21:15] <= offset[13:7];

  // A function that is not inlined: its argument is not a sensitivity
  function automatic logic [6:0] transform(input logic [6:0] x);
    // verilator no_inline_task
    return x ^ 7'h55;
  endfunction
  logic [6:0] tq;
  always_latch if (en) tq <= transform(d);

  // A part-select at a variable position
  logic [1:0] vsel;
  logic [2:0] vpos = 0;
  always @(posedge clk) vpos <= vpos == 3'd5 ? 3'd0 : vpos + 3'd1;
  always_latch if (en) vsel <= d[vpos+:2];

  // A constant select partly out of range
  logic [6:0] oor;
  // verilator lint_off SELRANGE
  always_latch if (en) oor <= l1[20:14];
  // verilator lint_on SELRANGE

  // A memory partially written, read at a variable index: sensitive to each element it reads,
  // so a flop on the edge opening the latch sees the previous value
  logic [7:0] mem[100];
  logic [6:0] ri = 1;
  logic [7:0] mem_sampled = 0;
  initial for (int i = 0; i < 100; ++i) mem[i] = 8'(i);
  always @(posedge clk) ri <= ri == 7'd99 ? 7'd1 : ri + 7'd1;
  always_latch if (en) mem[0] <= mem[ri];
  always @(posedge en) mem_sampled <= mem[0];

  // Not tracked, so still scheduled as combinational logic: a multidimensional array, and
  // values change detection can't compare (behavioral)
  logic [6:0] md[2][3];
  string str = "";
  int q[$];
  Cls h = new(0);
  always @(posedge clk) begin
    md[1][0] <= d;
    str <= {str, "x"};
    q.push_back(cyc);
    h = new(cyc);
  end
  int str_len, q_size, h_v;
  // verilator lint_off COMBDLY
  always_latch if (en) md[1][2] <= md[1][0];
  always_latch if (en) str_len <= str.len();
  always_latch if (en) q_size <= q.size();
  always_latch if (en) h_v <= h.v;
  // verilator lint_on COMBDLY

  // Reference model, evaluated when everything has settled
  logic [6:0] lp_r = 0, ln_r = 0, qp_r = 0, qn_r = 0, l4_r = 0;
  logic [14:0] l1_r = 0, l2_r = 0;
  logic [31:0] wide_q = 0;
  logic en_p_q = 0, en_n_q = 1;
  always @(negedge clk) begin
    if (en_p && !en_p_q) qp_r = lp_r;
    if (!en_n && en_n_q) qn_r = ln_r;
    if (en_p) lp_r = d;
    if (!en_n) ln_r = d;
    if (en_p) l1_r = {8'h5a, d};
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
      `checkh(t0_var, 33'h1_2345_6789);
      `checkh(t0_wire, 33'h1_2345_6789);
      `checkh(wide[64:33], wide[31:0]);
      `checkh(qw, wide_q);
      `checkh(stages[2], stages[1]);
      `checkh(words[1][6:0], words[1][13:7]);
      `checkh(words[3][6:0], words[3][13:7]);
      `checkh(tq, d ^ 7'h55);
      `checkh(vsel, d[vpos+:2]);
      `checkh(ascending[3:9], ascending[11:17]);
      `checkh(offset[21:15], offset[13:7]);
      `checkh(oor[0], l1[14]);
      `checkh(md[1][2], md[1][0]);
      `checkh(mem[0], mem[ri]);
      `checkh(mem_sampled, 0);
      `checkh(str_len, str.len());
      `checkh(q_size, q.size());
      `checkh(h_v, h.v);
    end
    wide_q = wide[31:0];
    if (cyc == 40) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
