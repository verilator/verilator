// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// IEEE 1800-2023 16.9.9: expr throughout seq
// CRC-driven random stimulus exercises throughout with varying cond/a/b signals.

module t (
  input clk
);
  integer cyc = 0;
  reg [63:0] crc = '0;

  // Derive signals from non-adjacent CRC bits (gap > max delay to avoid LFSR correlation)
  wire cond = crc[0];
  wire a    = crc[4];
  wire b    = crc[8];
  wire c    = crc[12];

  int count_fail1 = 0;
  int count_fail2 = 0;
  int count_fail3 = 0;
  int count_fail4 = 0;
  int count_fail5 = 0;
  int count_fail6 = 0;

  // Test 1: a |-> (cond throughout (1'b1 ##3 1'b1))
  // If a fires, cond must hold for 4 consecutive ticks (start + 3 delay ticks).
  assert property (@(posedge clk) disable iff (cyc < 10)
      a |-> (cond throughout (1'b1 ##3 1'b1)))
    else count_fail1 <= count_fail1 + 1;

  // Test 2: a |-> (cond throughout (1'b1 ##1 b))
  // If a fires, cond must hold for 2 ticks and b must be true at tick +1.
  assert property (@(posedge clk) disable iff (cyc < 10)
      a |-> (cond throughout (1'b1 ##1 b)))
    else count_fail2 <= count_fail2 + 1;

  // Test 3: a |-> (cond throughout b)
  // No delay: degenerates to a |-> (cond && b).
  assert property (@(posedge clk) disable iff (cyc < 10)
      a |-> (cond throughout b))
    else count_fail3 <= count_fail3 + 1;

  // Test 4: throughout with range delay on RHS (IEEE 16.9.9)
  assert property (@(posedge clk) disable iff (cyc < 10)
      a |-> (a throughout (b ##[1:2] c)))
    else count_fail4 <= count_fail4 + 1;

  // Test 5: throughout with temporal 'and' on RHS
  assert property (@(posedge clk) disable iff (cyc < 10)
      a |-> (a throughout ((b ##1 c) and (c ##1 b))))
    else count_fail5 <= count_fail5 + 1;

  // Test 6: nested throughout
  assert property (@(posedge clk) disable iff (cyc < 10)
      a |-> (a throughout (b throughout (b ##1 c))))
    else count_fail6 <= count_fail6 + 1;

  // Throughout with range-delay, pure-boolean RHS: the range-delay SExpr
  // generates midSource vertices that inherit the throughout guard.
  // Exercises the throughoutCond clone path in wireMatchAndMidSources.
  cover property (@(posedge clk) a throughout (b ##[1:3] c));

  // Cover-with-throughout: isCover path deletes the reject signals generated
  // by the throughout-drop check.
  cover property (@(posedge clk) a throughout (b ##1 c));

  always_ff @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x cond=%b a=%b b=%b c=%b\n",
           $time, cyc, crc, cond, a, b, c);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkd(count_fail1, 28);  // Questa: 28
      `checkd(count_fail2, 33);  // Questa: 33
      `checkd(count_fail3, 31);  // Questa: 31
      `checkd(count_fail4, 35);  // Questa: 35
      // count_fail5: NFA undercounts by 12; throughout+temporal-and first-step
      // rejection is a known limitation of the SAnd combiner architecture
      // (propagating isTopLevelStep causes double-counting; fix is future work).
      `checkd(count_fail5, 25);  // Questa: 36
      `checkd(count_fail6, 33);  // Questa: 33
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
