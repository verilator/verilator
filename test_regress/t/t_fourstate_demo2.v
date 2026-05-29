// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

task writeFourState(logic a);
  if (a === 1'b1) $write("1");
  else if (a === 1'b0) $write("0");
  else if (a === 1'bx) $write("x");
  else if (a === 1'bz) $write("z");
  else $stop;
endtask

module counter (
    input clk,
    input rstn,
    output reg [3:0] out
);
  always @(posedge clk) begin
    if (!rstn) out <= 0;
    else out <= out + 1;
  end
endmodule

module tb_counter;
  reg clk;
  reg rstn;
  wire [3:0] out;

  counter c (
      .clk (clk),
      .rstn(rstn),
      .out (out)
  );

  always #5 begin
    if (clk) begin
      $write("[out] ");
      writeFourState(out[3]);
      writeFourState(out[2]);
      writeFourState(out[1]);
      writeFourState(out[0]);
      $write("\n");
    end
    clk = ~clk;
  end

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
    #20 rstn = 1;
    #20 clk = 0;

    #25 rstn = 1;
    #20 rstn = 0;
    #10 rstn = 1;

    #100;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
