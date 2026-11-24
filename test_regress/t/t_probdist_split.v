// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic en;
  initial en = 1'b1;

  integer seed_e = 1234;
  integer seed_c = 1234;
  integer ref_e = 1234;
  integer ref_c = 1234;
  int cnt_e = 0;
  int cnt_c = 0;
  int cnt = 0;

  // The $dist functions write their seed, which nothing else in the block uses
  always @(posedge clk) begin
    if (($dist_erlang(seed_e, 5, 10) != 0) && en) cnt_e <= cnt_e + 1;
    if (($dist_chi_square(seed_c, 5) != 0) && en) cnt_c <= cnt_c + 1;
    if (en) cnt <= cnt + 1;
  end
  always @(posedge clk) void'($dist_erlang(ref_e, 5, 10));
  always @(posedge clk) void'($dist_chi_square(ref_c, 5));

  // The seed is also read in the block, and the condition guards two blocks' worth
  integer seed_u = 1234;
  integer ref_u = 1234;
  int cnt_a = 0;
  int cnt_b = 0;
  int seen_u;
  always @(posedge clk) begin
    if ($dist_uniform(seed_u, 0, 9) != 10) begin
      cnt_a <= cnt_a + 1;
      cnt_b <= cnt_b + 2;
    end
    seen_u <= seed_u;
  end
  always @(posedge clk) void'($dist_uniform(ref_u, 0, 9));

  // In a case selector, compared with each item
  integer seed_s = 1234;
  integer ref_s = 1234;
  int cnt_s[4] = '{0, 0, 0, 0};
  always @(posedge clk) begin
    case ($dist_uniform(seed_s, 0, 3))
      0: cnt_s[0] <= cnt_s[0] + 1;
      1: cnt_s[1] <= cnt_s[1] + 1;
      2: cnt_s[2] <= cnt_s[2] + 1;
      default: cnt_s[3] <= cnt_s[3] + 1;
    endcase
  end
  always @(posedge clk) void'($dist_uniform(ref_s, 0, 3));

  // In an inside expression, compared with each item
  integer seed_i = 1234;
  int cnt_i = 0;
  always @(posedge clk) begin
    if ($dist_uniform(seed_i, 0, 9) inside {[0 : 4], [5 : 9]}) cnt_i <= cnt_i + 1;
  end

  // The result is not used, the seed is
  integer seed_d = 1234;
  integer seed_p = 1234;
  int unused_d;
  int unused_p;
  always @(posedge clk) unused_d = $dist_uniform(seed_d, 0, 9);
  always @(posedge clk) unused_p = $dist_chi_square(seed_p, 5);

  always @(posedge clk) cyc <= cyc + 1;

  // Each seed is updated once per clock
  always @(negedge clk) begin
    `checkd(seed_e, ref_e);
    `checkd(seed_c, ref_c);
    `checkd(seed_u, ref_u);
    `checkd(seen_u, ref_u);
    `checkd(seed_s, ref_s);
    `checkd(seed_i, ref_u);
    `checkd(seed_d, ref_u);
    `checkd(seed_p, ref_c);
    `checkd(cnt_e, cyc);
    `checkd(cnt_c, cyc);
    `checkd(cnt, cyc);
    `checkd(cnt_a, cyc);
    `checkd(cnt_b, 2 * cyc);
    `checkd(cnt_s[0] + cnt_s[1] + cnt_s[2] + cnt_s[3], cyc);
    `checkd(cnt_i, cyc);
    if (cyc == 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
