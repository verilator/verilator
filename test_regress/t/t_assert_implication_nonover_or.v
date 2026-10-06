// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Marco Brambilla
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic a = 0, x = 0, y = 0;
  int fail_or = 0, fail_or_noparen = 0, fail_prop_or = 0, fail_multi_ante = 0;
  int fail_delay_or = 0, fail_and = 0;
  int cov_prop_or = 0, cov_prop_lor = 0, cov_seq_or = 0, cov_seq_lor = 0;

  // a in cycles 3, 6, 9, 12; the consequent cycle after each has
  //   cycle 4: x=0 y=0 -> every disjunction fails
  //   cycle 7: x=1 y=0, cycle 10: x=0 y=1, cycle 13: x=1 y=1 -> no disjunction fails
  assert property (@(posedge clk) a |=> (x || y))
  else fail_or = fail_or + 1;
  assert property (@(posedge clk) a |=> x || y)
  else fail_or_noparen = fail_or_noparen + 1;
  assert property (@(posedge clk) a |=> (x or y))
  else fail_prop_or = fail_prop_or + 1;
  assert property (@(posedge clk) a ##1 1 |-> (x || y))
  else fail_multi_ante = fail_multi_ante + 1;
  assert property (@(posedge clk) a |-> ##1 (x || y))
  else fail_delay_or = fail_delay_or + 1;
  assert property (@(posedge clk) a |=> (x && y))
  else fail_and = fail_and + 1;

  // x or y is true in cycles 7, 10 and 13
  cover property (@(posedge clk) x or y) cov_prop_or = cov_prop_or + 1;
  cover property (@(posedge clk) x || y) cov_prop_lor = cov_prop_lor + 1;
  cover sequence (@(posedge clk) x or y) cov_seq_or = cov_seq_or + 1;
  cover sequence (@(posedge clk) x || y) cov_seq_lor = cov_seq_lor + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    a <= (cyc == 2 || cyc == 5 || cyc == 8 || cyc == 11);
    x <= (cyc == 6 || cyc == 12);
    y <= (cyc == 9 || cyc == 12);
    if (cyc == 20) begin
      `checkd(fail_or, 1);
      `checkd(fail_or_noparen, 1);
      `checkd(fail_prop_or, 1);
      `checkd(fail_multi_ante, 1);
      `checkd(fail_delay_or, 1);
      `checkd(fail_and, 3);
      `checkd(cov_prop_or, 3);
      `checkd(cov_prop_lor, 3);
      `checkd(cov_seq_or, 3);
      `checkd(cov_seq_lor, 3);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
