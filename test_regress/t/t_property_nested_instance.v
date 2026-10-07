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

  int cyc;
  reg [63:0] crc;

  // Non-adjacent CRC bits to avoid LFSR shift correlation
  wire a = crc[0];
  wire b = crc[4];
  wire c = crc[8];

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
  int count_cover_nested = 0;
  int count_cover_inline = 0;

  property p_b;
    b;
  endproperty

  property p_arg(logic x);
    x;
  endproperty

  property p_outer;
    a |-> p_b;
  endproperty

  property p_top;
    c |-> p_outer;
  endproperty

  property p_loc;
    logic snap;
    (1, snap = c) |-> (b == snap);
  endproperty

  // Test 1/2: nested instance under implication vs inline body
  assert property (@(posedge clk) disable iff (cyc < 2) a |-> p_b)
  else count_fail1 <= count_fail1 + 1;

  assert property (@(posedge clk) disable iff (cyc < 2) a |-> b)
  else count_fail2 <= count_fail2 + 1;

  // Test 3/4: nested instance with an argument
  assert property (@(posedge clk) disable iff (cyc < 2) a |-> p_arg(c))
  else count_fail3 <= count_fail3 + 1;

  assert property (@(posedge clk) disable iff (cyc < 2) a |-> c)
  else count_fail4 <= count_fail4 + 1;

  // Test 5/6: nested instance under not
  assert property (@(posedge clk) disable iff (cyc < 2) not p_b)
  else count_fail5 <= count_fail5 + 1;

  assert property (@(posedge clk) disable iff (cyc < 2) not b)
  else count_fail6 <= count_fail6 + 1;

  // Test 7: nested instance inside another property's body, compared with test 2
  assert property (@(posedge clk) disable iff (cyc < 2) p_outer)
  else count_fail7 <= count_fail7 + 1;

  // Test 8/9: nested instance with a property-local variable vs inline body
  assert property (@(posedge clk) disable iff (cyc < 2) a |-> p_loc)
  else count_fail8 <= count_fail8 + 1;

  assert property (@(posedge clk) disable iff (cyc < 2) a |-> (b == c))
  else count_fail9 <= count_fail9 + 1;

  // Test 10: same property as test 3 with a different argument, compared with test 2
  assert property (@(posedge clk) disable iff (cyc < 2) a |-> p_arg(b))
  else count_fail10 <= count_fail10 + 1;

  // Test 11/12/13: two-level nesting, nested and through a top-level instance, vs inline body
  assert property (@(posedge clk) disable iff (cyc < 2) c |-> p_outer)
  else count_fail11 <= count_fail11 + 1;

  assert property (@(posedge clk) disable iff (cyc < 2) c |-> (a |-> b))
  else count_fail12 <= count_fail12 + 1;

  assert property (@(posedge clk) disable iff (cyc < 2) p_top)
  else count_fail13 <= count_fail13 + 1;

  // Cover: nested instance vs inline body, counted only with --coverage
  cover property (@(posedge clk) disable iff (cyc < 2) a |-> p_b)
    count_cover_nested <= count_cover_nested + 1;

  cover property (@(posedge clk) disable iff (cyc < 2) a |-> b)
    count_cover_inline <= count_cover_inline + 1;

  // Stimulus on negedge so properties sample stable values (see #7545)
  always @(negedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x a=%b b=%b c=%b\n", $time, cyc, crc, a, b, c);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc == 99) begin
      `checkh(crc, 64'hc77bb9b3784ea091);
      `checkd(count_fail1, 20);
      `checkd(count_fail2, 20);
      `checkd(count_fail3, 25);
      `checkd(count_fail4, 25);
      `checkd(count_fail5, 50);
      `checkd(count_fail6, 50);
      `checkd(count_fail7, 20);
      `checkd(count_fail8, 21);
      `checkd(count_fail9, 21);
      `checkd(count_fail10, 20);
      `checkd(count_fail11, 8);
      `checkd(count_fail12, 8);
      `checkd(count_fail13, 8);
`ifdef TEST_COVERAGE
      `checkd(count_cover_nested, 28);
      `checkd(count_cover_inline, 28);
`endif
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
