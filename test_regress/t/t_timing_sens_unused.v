// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`timescale 1ns / 1ps

module t;
  // Issue #9198: The body need not read the variable that triggers it.
  logic rst = 1'b0;
  time t_rst = 0;
  always @(rst) t_rst = $time;

  // Reading only part of the sensitivity list must retain the other triggers.
  logic select_value = 1'b0;
  time t_partial = 0;
  always @(rst or select_value) t_partial = $time + time'(select_value);

  // Writing the trigger is not a read dependency.
  logic write_trigger = 1'b0;
  always @(write_trigger) write_trigger = 1'b0;

  // Reading the trigger after overwriting it is not a read dependency either.
  logic overwritten_trigger = 1'b0;
  time t_overwritten = 0;
  always @(overwritten_trigger) begin
    overwritten_trigger = 1'b0;
    t_overwritten = $time + time'(overwritten_trigger);
  end

  // A complete sensitivity list can still be treated as combinational logic.
  logic [1:0] read_value;
  always @(rst or select_value) read_value = {rst, select_value};

  // Repeated reads must only consume a trigger once.
  time t_repeat = 0;
  always @(rst) t_repeat = $time + time'(rst) + time'(rst);

  initial begin
    #5 select_value = 1'b1;
  end

  initial begin
    #10 rst = 1'b1;
    write_trigger = 1'b1;
    overwritten_trigger = 1'b1;
    #1;
    `checkd(t_rst, 10);
    `checkd(t_partial, 11);
    `checkd(write_trigger, 1'b0);
    `checkd(t_overwritten, 10);
    `checkd(read_value, 2'b11);
    `checkd(t_repeat, 12);
    #10 rst = 1'b0;
    write_trigger = 1'b1;
    overwritten_trigger = 1'b1;
    #1;
    `checkd(t_rst, 21);
    `checkd(t_partial, 22);
    `checkd(write_trigger, 1'b0);
    `checkd(t_overwritten, 21);
    `checkd(read_value, 2'b01);
    `checkd(t_repeat, 21);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
