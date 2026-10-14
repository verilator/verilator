// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Kristof Marien
// SPDX-License-Identifier: CC0-1.0

// A clocking block output driving an input port through a connection that
// cannot be decomposed (arithmetic) is unsupported: the drive has nowhere
// to flow.

interface sender_if (
    input wire clk,
    input wire [7:0] bus
);
  clocking sender_cb @(posedge clk);
    default input #1step output #1step;
    output bus;
  endclocking
  task drive(input logic [7:0] value);
    sender_cb.bus <= value;
    @(sender_cb);
  endtask
endinterface

module dut (
    input wire clk,
    input wire [7:0] a,
    input wire [7:0] b
);
  sender_if sender (.clk(clk), .bus(a + b));
endmodule

module t;
  logic clk = 0;
  logic [7:0] a = 8'h11;
  logic [7:0] b = 8'h22;
  dut d (.clk(clk), .a(a), .b(b));

  always #5 clk = ~clk;
endmodule
