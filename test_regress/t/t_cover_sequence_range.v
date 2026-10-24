// DESCRIPTION: Verilator: Bounded cover sequence delay rings
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
  int hits_implicit = 0;
  bit a = 0;
  bit b = 0;
  bit rst = 1;
  bit [31:0] crc = 32'h5aef0c8d;

  cover sequence (@(posedge clk) ##[1:3] (cyc == 3)) hits_implicit++;
  // CHECK_COVER(-1,"top.t","cover",3)
  final `checkd(hits_implicit, 3);

  range_check #(
      .LO(0),
      .HI(257)
  ) zero_min (
      .*
  );
  range_check #(
      .LO(1),
      .HI(258)
  ) one_min (
      .*
  );
  range_check #(
      .LO(3),
      .HI(260)
  ) fixed_prefix (
      .*
  );
  range_check #(
      .LO(1),
      .HI(300)
  ) reported (
      .*
  );
  range_check #(
      .LO(1),
      .HI(3)
  ) small_range (
      .*
  );
  range_check #(
      .LO(0),
      .HI(1)
  ) adjacent (
      .*
  );
  range_check #(
      .LO(3),
      .HI(259)
  ) boundary (
      .*
  );

  always @(negedge clk) begin
    if (cyc == 1000) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
    rst = (cyc == 500 || cyc == 501);
    crc = {crc[30:0], crc[31] ^ crc[21] ^ crc[1] ^ crc[0]};
    // Isolated starts, full windows across wraps, draining, then varied traffic.
    if (cyc < 330) begin
      a = (cyc == 0 || cyc == 2);
      b = 1;
    end
    else if (cyc < 650) begin
      a = 1;
      b = 1;
    end
    else if (cyc >= 730) begin
      a = 0;
      b = 1;
    end
    else begin
      a = crc[0];
      b = crc[9];
    end
    cyc++;
  end
endmodule

module range_check #(
    parameter int LO = 1,
    parameter int HI = 300
) (
    input clk,
    input a,
    input b,
    input rst
);
  bit [HI:0] history = '0;
  bit [HI:0] history_disabled = '0;
  int hits = 0;
  int hits_disabled = 0;
  int expected = 0;
  int expected_disabled = 0;

  cover sequence (@(posedge clk) a ##[LO:HI] b) hits++;
  // CHECK_COVER(-1,"top.t.zero_min","cover",81961)
  // CHECK_COVER(-2,"top.t.one_min","cover",81942)
  // CHECK_COVER(-3,"top.t.fixed_prefix","cover",81892)
  // CHECK_COVER(-4,"top.t.reported","cover",94982)
  // CHECK_COVER(-5,"top.t.small_range","cover",1017)
  // CHECK_COVER(-6,"top.t.adjacent","cover",673)
  // CHECK_COVER(-7,"top.t.boundary","cover",81578)
  cover sequence (@(posedge clk) disable iff (rst) a ##[LO:HI] b) hits_disabled++;
  // CHECK_COVER(-1,"top.t.zero_min","cover",55021)
  // CHECK_COVER(-2,"top.t.one_min","cover",54876)
  // CHECK_COVER(-3,"top.t.fixed_prefix","cover",54577)
  // CHECK_COVER(-4,"top.t.reported","cover",62540)
  // CHECK_COVER(-5,"top.t.small_range","cover",1005)
  // CHECK_COVER(-6,"top.t.adjacent","cover",668)
  // CHECK_COVER(-7,"top.t.boundary","cover",54391)

  // Each bit represents a distinct start, including the current tick at bit zero.
  always @(posedge clk) begin
    history = {history[HI-1:0], a};
    if (b) expected += $countones(history[HI:LO]);
  end
  always @(posedge clk or posedge rst) begin
    if (rst) history_disabled = '0;
    else begin
      history_disabled = {history_disabled[HI-1:0], a};
      if (b) expected_disabled += $countones(history_disabled[HI:LO]);
    end
  end

  // The action blocks have completed before the falling edge.
  always @(negedge clk) begin
    `checkd(hits, expected);
    `checkd(hits_disabled, expected_disabled);
  end
  final begin
    `checkd(hits, expected);
    `checkd(hits_disabled, expected_disabled);
    `checkd(hits > 0, 1'b1);
    `checkd(hits_disabled > 0, 1'b1);
  end
endmodule
