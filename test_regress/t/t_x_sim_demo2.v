// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module counter(input clk, input rstn, output reg[3:0] out);
  always @(posedge clk) begin
    if (!rstn) out <= 0;
    else out <= out + 1;
  end
endmodule

module tb_counter;
  reg clk;
  reg rstn;
  wire [3:0] out;

  counter c(.clk (clk),
            .rstn (rstn),
            .out (out));

  always #5 begin
    if (clk) $write("[out] %d\n", out);
    clk = ~clk;
  end

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
    #20 rstn <= 1;
    #20 clk <= 0;

    #25 rstn <= 1;
    #20 rstn <= 0;
    #10 rstn <= 1;

    #100 $finish;
  end
endmodule
