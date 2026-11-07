// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  localparam int MIN_N = 3;

  int cyc;
  reg [63:0] crc;

  // Derive signals from non-adjacent CRC bits
  wire a = crc[0];
  wire b = crc[4];
  wire c = crc[8];
  wire d = crc[12];

  int count_fail1 = 0;
  int count_fail2 = 0;
  int count_fail3 = 0;
  int count_fail4 = 0;
  int count_fail5 = 0;
  int count_fail6 = 0;
  int count_fail7 = 0;
  int count_fail8 = 0;
  int count_fail9 = 0;
  int count_fail10 = 0;
  int count_fail11 = 0;
  int count_fail12 = 0;
  int count_fail13 = 0;
  int count_fail14 = 0;
  int count_fail15 = 0;
  int count_fail16 = 0;
  int count_fail17 = 0;
  int count_fail18 = 0;
  int count_fail19 = 0;
  int count_fail20 = 0;
  int count_fail21 = 0;
  int count_fail22 = 0;
  int count_fail23 = 0;
  int count_fail24 = 0;

  unbounded_rep_reject_test unboundedRepRejectTest (clk);
  unbounded_rep_match_item_test unboundedRepMatchItemTest (clk);

  // Test 1: a[*3] |-> b
  assert property (@(posedge clk) a [* 3] |-> b)
  else count_fail1 <= count_fail1 + 1;

  // Test 2: a[*1] |-> c
  assert property (@(posedge clk) a [* 1] |-> c)
  else count_fail2 <= count_fail2 + 1;

  // Test 3: a[*2] |=> d
  assert property (@(posedge clk) a [* 2] |=> d)
  else count_fail3 <= count_fail3 + 1;

  // Test 4: b[*2] standalone
  assert property (@(posedge clk) b [* 2])
  else count_fail4 <= count_fail4 + 1;

  // Test 5: a[*10000] large count
  assert property (@(posedge clk) a [* 100] |-> b)
  else count_fail5 <= count_fail5 + 1;

  // Test 6: a[*1:3] ##1 b -- bounded range in SExpr
  assert property (@(posedge clk) a [* 1:3] ##1 b)
  else count_fail6 <= count_fail6 + 1;

  // Test 7: a[+] ##1 b -- one-or-more in SExpr
  assert property (@(posedge clk) a [+] ##1 b)
  else count_fail7 <= count_fail7 + 1;

  // Test 8: a[+] |-> b -- standalone [+]
  assert property (@(posedge clk) a [+] |-> b)
  else count_fail8 <= count_fail8 + 1;

  // Test 9: a[*] |-> b -- standalone [*]
  assert property (@(posedge clk) a [*] |-> b)
  else count_fail9 <= count_fail9 + 1;

  // Test 10: a[*1] ##1 b -- trivial [*1] in SExpr (restored to plain SExpr)
  assert property (@(posedge clk) a [* 1] ##1 b)
  else count_fail10 <= count_fail10 + 1;

  // Test 11: a[*] ##1 b -- zero-or-more in SExpr (minN==0 path)
  assert property (@(posedge clk) a [*] ##1 b)
  else count_fail11 <= count_fail11 + 1;

  // Parenthesized sampled-value functions followed by consecutive repetition
  assert property (@(posedge clk) ($stable(1'b0)) [+]);
  assert property (@(posedge clk) ($stable(a)) [+] |-> 1'b1);
  assert property (@(posedge clk) ($stable(a, clk)) [+] |-> 1'b1);
  assert property (@(posedge clk) ($fell(a)) [+] |-> 1'b1);
  assert property (@(posedge clk) ($past(a)) [+] |-> 1'b1);
  assert property (@(posedge clk) ($rose(a)) [+] |-> 1'b1);
  assert property (@(posedge clk) ($changed(a)) [+] |-> 1'b1);

  // Tests 12-13: explicit unbounded aliases
  assert property (@(posedge clk) a [*0:$] ##1 b)
  else count_fail12 <= count_fail12 + 1;
  assert property (@(posedge clk) a [*1:$] ##1 b)
  else count_fail13 <= count_fail13 + 1;

  // Tests 14-17: IEEE 1800-2023 F.3.4.2.1 expansion of arbitrary minima
  assert property (@(posedge clk) a [*2:$] ##1 b)
  else count_fail14 <= count_fail14 + 1;
  assert property (@(posedge clk) a ##1 a [+] ##1 b)
  else count_fail15 <= count_fail15 + 1;
  assert property (@(posedge clk) a [*MIN_N:$] ##1 b)
  else count_fail16 <= count_fail16 + 1;
  assert property (@(posedge clk) a [*2] ##1 a [+] ##1 b)
  else count_fail17 <= count_fail17 + 1;

  // Tests 18-21: unbounded repetition in antecedent and consequent positions
  assert property (@(posedge clk) a [*2:$] |-> b)
  else count_fail18 <= count_fail18 + 1;
  assert property (@(posedge clk) (a ##1 a [+]) |-> b)
  else count_fail19 <= count_fail19 + 1;
  assert property (@(posedge clk) c |-> a [*2:$])
  else count_fail20 <= count_fail20 + 1;
  assert property (@(posedge clk) c |-> (a ##1 a [+]))
  else count_fail21 <= count_fail21 + 1;

  // Test 22: Fail the middle required check of an exact repetition.
  assert property (@(posedge clk) cyc == 1 |-> ##1 (cyc != 3) [*3])
  else count_fail22 <= count_fail22 + 1;

  // Test 23: A bounded range succeeds at its minimum, later repetitions are optional.
  assert property (@(posedge clk) cyc == 1 |-> ##1 (cyc != 5) [*3:5])
  else count_fail23 <= count_fail23 + 1;

  // Test 24: The empty endpoint of [*0:1] must not remain live for a later match.
  assert property (@(posedge clk) cyc == 1 |-> (cyc == 2) [*0:1] ##1 (cyc == 2))
  else count_fail24 <= count_fail24 + 1;

  // Counter FSM with M>0: range > kChainLimit (256) forces counter vertex
  // creation; min>0 exercises the Gte/active gating path in resolveLinks and
  // emitNbaLogic. Cover-only so count_fail values above are undisturbed.
  cover property (@(posedge clk) ##[10:300] b);

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x a=%b b=%b c=%b d=%b\n", $time, cyc, crc, a, b, c, d);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkd(count_fail1, 5);
      `checkd(count_fail2, 25);  // One other sim: 19
      `checkd(count_fail3, 9);
      `checkd(count_fail4, 49);
      `checkd(count_fail5, 0);
      // NFA merge-node range [*M:N] over-counts rejects; match
      // detection is correct, only reject counting is imprecise
      `checkd(count_fail6, 59);  // All other sims: 51
      `checkd(count_fail7, 51);
      `checkd(count_fail8, 20);
      // IEEE 1800-2023 16.9.2 permits empty match of [*0]; NFA reports
      // rejects on each tick while others suppress
      `checkd(count_fail9, 49);  // Most others: 20, one other 49
      `checkd(count_fail10, 59);
      // a[*] ##1 b: NFA treats unbounded [*] as liveness (no reject);
      // Should be definite antecedent
      `checkd(count_fail11, 0);  // All other sims: 29
      `checkd(count_fail12, count_fail11);
      `checkd(count_fail13, count_fail7);
      `checkd(count_fail14, count_fail15);
      `checkd(count_fail16, count_fail17);
      `checkd(count_fail18, count_fail19);
      `checkd(count_fail20, count_fail21);
      `checkd(count_fail22, 1);
      `checkd(count_fail23, 0);
      `checkd(count_fail24, 1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

// A sequence match item after an unbounded repetition is legal and must not
// be mistaken for a side effect in the endpoint's boolean expression.
module unbounded_rep_match_item_test (input logic clk);
  logic start = 0;
  logic a = 0;
  logic b = 0;
  logic start_overlap = 0;
  logic a_overlap = 1;
  logic b_overlap = 0;
  int passes = 0;
  int failures = 0;
  int overlap_match_items = 0;
  int overlap_failures = 0;
  logic disable_match = 0;
  logic disable_start = 0;
  logic disable_a = 0;
  logic disable_b = 0;
  int disable_failures = 0;

  property p;
    int x;
    start |-> a [*1:$] ##0 (b, x = 1);
  endproperty

  assert property (@(posedge clk) p)
  passes++;
  else failures++;

  property p_disable;
    int y;
    disable iff (disable_match)
      disable_start |-> disable_a [*1:$] ##0 (disable_b, y = 1);
  endproperty

  assert property (@(posedge clk) p_disable)
  else disable_failures++;

  function void count_overlap_match();
    overlap_match_items++;
  endfunction

  assert property (@(posedge clk)
    start_overlap |-> a_overlap [*1:$] ##0 (b_overlap, count_overlap_match()))
  else overlap_failures++;

  initial begin
    @(negedge clk);
    start = 1;
    a = 1;
    @(negedge clk);
    start = 0;
    b = 1;
    @(negedge clk);
    a = 0;
    b = 0;
    repeat (2) @(posedge clk);
    `checkh(passes, 1);
    `checkh(failures, 0);

    @(negedge clk);
    disable_start = 1;
    disable_a = 1;
    @(negedge clk);
    disable_start = 0;
    disable_b = 1;
    disable_match = 1;
    @(negedge clk);
    disable_match = 0;
    disable_a = 0;
    disable_b = 0;
    repeat (2) @(posedge clk);
    `checkh(disable_failures, 0);

    // Two overlapping attempts match the endpoint on the same tick. Each
    // match item must execute once, even though both attempts share NFA state.
    @(negedge clk);
    start_overlap = 1;
    @(negedge clk);
    b_overlap = 1;
    @(negedge clk);
    start_overlap = 0;
    b_overlap = 0;
    repeat (2) @(posedge clk);
    `checkh(overlap_match_items, 2);
    `checkh(overlap_failures, 0);
  end
endmodule

// Directed checks for failed unbounded repetitions and a later ranged-delay
// candidate. Kept with the consecutive-repetition tests.
module unbounded_rep_reject_test (input logic clk);
  logic psel = 0;
  logic paddr = 0;
  logic pready = 0;
  logic psel_no_endpoint = 0;
  logic paddr_no_endpoint = 0;
  logic pready_no_endpoint = 0;
  logic range_start = 0;
  logic range_x = 0;
  logic range_a = 0;
  logic range_b = 0;
  logic disable_reset = 0;
  logic disable_start = 0;
  logic disable_a = 1;
  logic disable_b = 0;
  logic replay_a = 1;
  int failures = 0;
  int no_endpoint_failures = 0;
  int range_passes = 0;
  int range_failures = 0;
  int disable_failures = 0;
  int replay_failures = 0;
  time replay_failure_times [0:3];
  int cycle = 0;
  int start_cycle = 0;
  int failure_cycle = 0;
  int no_endpoint_failure_cycle = 0;

  always @(posedge clk) cycle <= cycle + 1;

  assert property (@(posedge clk)
    $rose(psel) |->
    ($rose(psel) ##1 ((!$changed(paddr))[*1:$] ##0 (pready == 1))))
  else begin
    failures++;
    failure_cycle = cycle;
  end

  assert property (@(posedge clk)
    $rose(psel_no_endpoint) |->
    ($rose(psel_no_endpoint) ##1 ((!$changed(paddr_no_endpoint))[*1:$]
                                  ##0 (pready_no_endpoint == 1))))
  else begin
    no_endpoint_failures++;
    no_endpoint_failure_cycle = cycle;
  end

  assert property (@(posedge clk)
    range_start |-> ##[0:2] (range_x ##0 range_a[*1:$] ##0 range_b))
  range_passes++;
  else range_failures++;

  assert property (@(posedge clk) disable iff (disable_reset)
    disable_start |-> disable_a[*1:$] ##0 disable_b)
  else disable_failures++;

  // Several live repetitions can fail on the same sample; replay each failure action.
  assert property (@(posedge clk) replay_a[*1:$] ##0 1'b0)
  else begin
    if (replay_failures < 4) replay_failure_times[replay_failures] = $time;
    replay_failures++;
  end

  initial begin
    repeat (2) @(negedge clk);
    range_start = 1;
    range_x = 1;
    range_a = 1;
    @(negedge clk);
    range_start = 0;
    range_x = 0;
    range_a = 0;
    @(negedge clk);
    range_x = 1;
    range_a = 1;
    range_b = 1;
    @(negedge clk);
    `checkh(range_passes, 1);
    `checkh(range_failures, 0);
  end

  initial begin
    $assertvacuousoff(0);
    repeat (2) @(negedge clk);
    psel = 1;
    psel_no_endpoint = 1;
    start_cycle = cycle;
    @(negedge clk);
    paddr = 1;
    paddr_no_endpoint = 1;
    pready = 1;
    repeat (3) @(posedge clk);
    `checkh(failures, 1);
    `checkh(failure_cycle, start_cycle + 1);
    `checkh(no_endpoint_failures, 1);
    `checkh(no_endpoint_failure_cycle, start_cycle + 1);
  end

  initial begin
    repeat (2) @(negedge clk);
    disable_start = 1;
    @(negedge clk);
    disable_start = 0;
    disable_reset = 1;
    @(negedge clk);
    disable_reset = 0;
    repeat (2) @(posedge clk);
    `checkh(disable_failures, 0);
  end

  initial begin
    repeat (2) @(posedge clk);
    @(negedge clk);
    replay_a = 0;
    repeat (2) @(posedge clk);
    @(negedge clk);
    `checkh(replay_failures, 4);
    `checkh(replay_failure_times[0] == replay_failure_times[1], 1);
    `checkh(replay_failure_times[1] == replay_failure_times[2], 1);
    `checkh(replay_failure_times[3] > replay_failure_times[2], 1);
  end
endmodule
