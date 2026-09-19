// DESCRIPTION: Verilator: Bounded property delay rings
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;

  range_check #(
      .LO(0),
      .HI(1)
  ) adjacent (
      .*
  );
  range_check #(
      .LO(1),
      .HI(3)
  ) small_range (
      .*
  );
  range_check #(
      .LO(3),
      .HI(259)
  ) boundary (
      .*
  );
  range_check #(
      .LO(1),
      .HI(258)
  ) above_boundary (
      .*
  );
  range_check #(
      .LO(1),
      .HI(300)
  ) reported (
      .*
  );

  always @(negedge clk) begin
    // The last start is sampled at 666, expires at 967, and drains at 968.
    if (cyc == 968) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    cyc <= cyc + 1;
  end
endmodule

module range_check #(
    parameter int LO = 1,
    parameter int HI = 300
) (
    input clk,
    input int cyc
);
  bit a = 0;
  bit b = 0;
  bit c = 0;
  bit rst = 1;
  bit previous_b = 0;
  bit [HI:0] pending = '0;
  bit [HI+1:0] pending_nested = '0;
  int failures = 0;
  int failures_nested = 0;
  int expected = 0;
  int expected_nested = 0;

  assert property (@(posedge clk) disable iff (rst) a |-> ##[LO:HI] b)
  else failures++;
  assert property (@(posedge clk) disable iff (rst) a |-> ##[LO:HI] (b ##1 c))
  else failures_nested++;

  // Retain each attempt until a match clears it or its last endpoint expires.
  always @(posedge clk) begin
    if (rst) begin
      pending = '0;
      pending_nested = '0;
      previous_b = 0;
    end
    else begin
      pending = {pending[HI-1:0], a};
      pending_nested = {pending_nested[HI:0], a};
      if (b) pending[HI:LO] = '0;
      if (previous_b && c) pending_nested[HI+1:LO+1] = '0;
      if (pending[HI]) expected++;
      if (pending_nested[HI+1]) expected_nested++;
      previous_b = b;
    end
  end

  always @(negedge clk) begin
    `checkd(failures, expected);
    `checkd(failures_nested, expected_nested);
    rst = (cyc == 615);
    // Early and last endpoints precede attempts that must expire without a match.
    a = (cyc == 1 || cyc == 3 || cyc == HI + 3 || cyc == HI + 4 || (cyc >= 306 && cyc <= 321));
    b = (cyc == LO + 1 || cyc == HI + 1);
    c = (cyc == HI + 2);
    // Overlapping attempts and fresh matches exercise repeated ring wraps.
    if (cyc >= 616 && cyc <= 665) begin
      a = 1;
      // Preserve the input pattern while moving the burst fifteen cycles earlier.
      b = ((cyc + 15) % 13 == 0);
      c = ((cyc + 15) % 7 == 0);
    end
  end

  final begin
    `checkd(pending, '0);
    `checkd(pending_nested, '0);
    `checkd(failures, expected);
    `checkd(failures_nested, expected_nested);
    `checkd(failures > 0, 1'b1);
    `checkd(failures_nested > 0, 1'b1);
  end
endmodule
