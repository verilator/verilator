// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Alias type check error test.
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module s (
    input clk,
    output wire rdy,
    input reset
);
  parameter ss = 5;
  localparam w = 1 << ss;
  reg [ss-1:0] bitl;
  assign rdy = bitl[ss-1];
  (* ivl_synthesis_on *)
  always @(posedge clk or posedge reset) begin
    if (!reset) begin
      bitl <= bitl - 1;
    end
  end
endmodule
module t;
  parameter ss = 5;
  parameter w = 1 << ss;
  reg clk, reset;
  wire done;
  s dut (
      .clk  (clk),
      .rdy  (done),
      .reset(reset)
  );
  always #5 clk = !clk;
  task reset_dut;
    reset = 1;
    @(posedge clk);
    #1 reset = 0;
  endtask
  task run_dut;
    while (done == 0) begin
      @(posedge clk);
    end
  endtask
  initial begin
    clk = 0;
    reset_dut;
    run_dut;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
