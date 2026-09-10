// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Toru Niina
// SPDX-License-Identifier: CC0-1.0

`default_nettype none
`timescale 1ns / 1ps

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: off
//
`define expected_start_time 95
`define expected_end_time   190

module t;

  localparam cycle = 1000.0 / 100.0;
  localparam halfcycle = 0.5 * cycle;

  logic clk = '0;

  import "DPI-C" context task tb_c_wait();

  export "DPI-C" task tb_sv_wait;
  task automatic tb_sv_wait(input int n);
    $display("[%t] tb_sv_wait start...\n", $time);
    `checkd($time, `expected_start_time);
    repeat (n) @(negedge clk);
    `checkd($time, `expected_end_time);
    $display("[%t] tb_sv_wait done!\n", $time);
  endtask

  always #halfcycle clk = ~clk;

  initial begin
    $display("[%t] test start\n", $time);
    repeat (10) @(posedge clk);
    $display("[%t] calling tb_c_wait...\n", $time);
    `checkd($time, `expected_start_time);
    tb_c_wait();
    `checkd($time, `expected_end_time);
    $display("[%t] tb_c_wait finish\n", $time);
    repeat (10) @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial #(cycle * 30) $stop;  // timeout
endmodule
