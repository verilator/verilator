// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

module t (
    input clk
);
  localparam int BIG_DELAY = 1024;
  localparam int END_CYC = BIG_DELAY + 300;

  int cyc = 0;
  int fixed_pass_q[$];
  int fixed_fail_q[$];
  int range_pass_q[$];
  int range_fail_q[$];

  // Fixed delay: starts 1..12. Odd starts pass; even starts fail.
  wire fixed_a = (cyc >= 1 && cyc <= 12);
  wire fixed_b = (cyc == BIG_DELAY + 1) || (cyc == BIG_DELAY + 3)
                 || (cyc == BIG_DELAY + 5) || (cyc == BIG_DELAY + 7)
                 || (cyc == BIG_DELAY + 9) || (cyc == BIG_DELAY + 11);

  // Range delay: single passing starts match 10 cycles later. Two blocks never
  // match and expire 300 cycles after each start.
  wire range_pass_a = (cyc == 10) || (cyc == 40) || (cyc == 70) || (cyc == 100)
                      || (cyc == 130) || (cyc == 600) || (cyc == 640)
                      || (cyc == 680) || (cyc == 720);
  wire range_fail_a = (cyc >= 250 && cyc <= 257) || (cyc >= 820 && cyc <= 827);
  wire range_a = range_pass_a || range_fail_a;
  wire range_b = (cyc == 20) || (cyc == 50) || (cyc == 80) || (cyc == 110)
                 || (cyc == 140) || (cyc == 610) || (cyc == 650) || (cyc == 690)
                 || (cyc == 730);

  // Questa action blocks observe the cycle after the sampled property cycle.
  cover property (@(posedge clk) fixed_a ##1024 fixed_b) fixed_pass_q.push_back($sampled(cyc) + 1);

  assert property (@(posedge clk) fixed_a |-> ##1024 fixed_b)
  else fixed_fail_q.push_back($sampled(cyc) + 1);

  cover property (@(posedge clk) range_a ##[5:300] range_b) range_pass_q.push_back($sampled(cyc) + 1);

  assert property (@(posedge clk) range_a |-> ##[5:300] range_b)
  else range_fail_q.push_back($sampled(cyc) + 1);

  assert property (@(posedge clk)
      1'b0 |-> (fixed_a throughout (range_a throughout (range_b ##40 fixed_b))));

  assert property (@(posedge clk) 1'b0 |-> ##[5:300] (range_b ##1 fixed_b));

  assert property (@(posedge clk) 1'b0 |-> (fixed_a throughout (range_a ##[5:300] range_b)));

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == END_CYC) begin
      `checkp(fixed_pass_q, "'{'h402, 'h404, 'h406, 'h408, 'h40a, 'h40c}");
      `checkp(fixed_fail_q, "'{'h403, 'h405, 'h407, 'h409, 'h40b, 'h40d}");
      `checkp(range_pass_q, "'{'h15, 'h33, 'h51, 'h6f, 'h8d, 'h263, 'h28b, 'h2b3, 'h2db}");
      `checkp(range_fail_q,
              "'{'h227, 'h228, 'h229, 'h22a, 'h22b, 'h22c, 'h22d, 'h22e, 'h461, 'h462, 'h463, 'h464, 'h465, 'h466, 'h467, 'h468}");

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
