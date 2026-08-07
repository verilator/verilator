// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  bit clk = 0;
  int cyc = 0;
  bit a = 0, b = 0, c = 0, abrt = 0, abrt2 = 0;
  int fail_bool = 0;
  int fail_seq = 0;
  int pass_always = 0;
  int fail_always = 0;
  int fail_ring = 0;
  int fail_first = 0;
  int pass_rej = 0;
  int fail_rej = 0;
  int fail_nested = 0;
  int fail_nested_rej = 0;
  int fail_nested_rej_ref = 0;
  int fail_range = 0;
  int fail_ring2 = 0;
  int fail_rep_a = 0;
  int fail_rep_r = 0;
  int fail_rep_ring = 0;
  int fail_rep_ref = 0;
  int fail_rep_ring_true = 0;
  int fail_rep_ref_true = 0;
  int fail_goto = 0;
  int fail_goto2 = 0;
  int fail_goto_range = 0;
  int fail_goto_range2 = 0;
  int fail_delay = 0;
  int fail_fby = 0;
  int fail_and = 0;
  int fail_unb = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    a <= cyc[0];
    b <= cyc[1];
    c <= cyc[2];
    abrt <= (cyc == 7);
    abrt2 <= (cyc == 9);
  end

  assert property (@(posedge clk) sync_accept_on (abrt) (b |-> c))
  else fail_bool++;
  assert property (@(posedge clk) sync_accept_on (abrt) ((a ##1 b) |-> c))
  else fail_seq++;

  assert property (@(posedge clk) sync_accept_on (1'b1) (1'b1 |-> (1'b1 ##1 1'b0))) pass_always++;
  else fail_always++;

  assert property (@(posedge clk) sync_accept_on (abrt) (1'b1 ##2 c))
  else fail_ring++;

  assert property (@(posedge clk) sync_accept_on (1'b0) (b ##1 1'b1))
  else fail_first++;

  assert property (@(posedge clk) sync_reject_on (abrt) (1'b1 ##1 1'b1)) pass_rej++;
  else fail_rej++;

  assert property (@(posedge clk)
                  sync_accept_on (abrt) (1'b1 |-> sync_reject_on (1'b0) (1'b1 ##1 c)))
  else fail_nested++;

  assert property (@(posedge clk)
                  sync_reject_on (abrt)
                      sync_reject_on (a) (1'b1 throughout (1'b1 ##2 1'b1)))
  else fail_nested_rej++;
  assert property (@(posedge clk)
                  sync_reject_on (abrt || a) (1'b1 throughout (1'b1 ##2 1'b1)))
  else fail_nested_rej_ref++;

  assert property (@(posedge clk) sync_accept_on (abrt) (1'b1 ##[1:2] (a ##1 b)))
  else fail_range++;

  assert property (@(posedge clk) sync_accept_on (abrt) sync_accept_on (b) (1'b1 ##2 c))
  else fail_ring2++;

  assert property (@(posedge clk) sync_accept_on (abrt) (a [* 2]))
  else fail_rep_a++;

  assert property (@(posedge clk) sync_reject_on (abrt) (b [* 2]))
  else fail_rep_r++;

  assert property (@(posedge clk) sync_reject_on (abrt) (b [* 5]))
  else fail_rep_ring++;
  assert property (@(posedge clk) sync_reject_on (abrt) (b ##1 b ##1 b ##1 b ##1 b))
  else fail_rep_ref++;
  assert property (@(posedge clk) sync_reject_on (abrt) (1'b1 [* 5]))
  else fail_rep_ring_true++;
  assert property (@(posedge clk)
                  sync_reject_on (abrt) (1'b1 ##1 1'b1 ##1 1'b1 ##1 1'b1 ##1 1'b1))
  else fail_rep_ref_true++;

  assert property (@(posedge clk) sync_reject_on (abrt) (b [-> 5]))
  else fail_goto++;
  assert property (@(posedge clk) sync_reject_on (abrt2) (c [-> 5]))
  else fail_goto2++;
  assert property (@(posedge clk) sync_reject_on (abrt) (b [-> 3:5]))
  else fail_goto_range++;
  assert property (@(posedge clk) sync_reject_on (abrt2) (c [-> 3:5]))
  else fail_goto_range2++;

  assert property (@(posedge clk) sync_reject_on (abrt) (##1 c))
  else fail_delay++;

  cover property (@(posedge clk) (a ##1 b) or(sync_reject_on (abrt) (b ##1 c)));

  assert property (@(posedge clk) sync_reject_on (1'b0) (a #-# b))
  else fail_fby++;

  assert property (@(posedge clk) (sync_accept_on (abrt) b) and c)
  else fail_and++;

  assert property (@(posedge clk) sync_reject_on (abrt) (a and always [1:$] b))
  else fail_unb++;

  cover property (@(posedge clk) (a and b) ##1 c);


  initial begin
    repeat (40) #5 clk = ~clk;
    `checkd(fail_bool, 5);
    `checkd(fail_seq, 3);
    `checkd(pass_always, 20);
    `checkd(fail_always, 0);  // zero-ok
    `checkd(fail_ring, 8);
    `checkd(fail_first, 11);
    `checkd(pass_rej, 17);
    `checkd(fail_rej, 2);
    `checkd(fail_nested, 10);
    `checkd(fail_nested_rej_ref, 29);
    `checkd(fail_nested_rej, fail_nested_rej_ref);
    `checkd(fail_range, 6);
    `checkd(fail_ring2, 1);
    `checkd(fail_rep_a, 19);
    `checkd(fail_rep_r, 16);
    `checkd(fail_rep_ref, 19);
    `checkd(fail_rep_ring, fail_rep_ref);
    `checkd(fail_rep_ref_true, 5);
    `checkd(fail_rep_ring_true, fail_rep_ref_true);
    `checkd(fail_goto, 9);
    `checkd(fail_goto2, 6);
    `checkd(fail_goto_range, 10);
    `checkd(fail_goto_range2, 6);
    `checkd(fail_delay, 12);
    `checkd(fail_fby, 16);
    `checkd(fail_and, 16);
    `checkd(fail_unb, 3);  // One other sim: 19
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
