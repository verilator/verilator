// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module test_mod(input reg clk, input reg reset, output integer result);
  always @(reset) begin
    result <= 1;
  end
endmodule

module Dut(input clk);
  integer num;
  integer result1;
  integer result2;
  reg reset1;
  reg reset2;
  initial begin
    reset1 = $random;
    reset2 = $random;
  end
  always @(posedge clk) begin
    num <= num + 1;
    if (num == 5) begin
      reset1 <= 1'b1;
    end
    if (num == 10) begin
      // display to prevent optimalization
      $display("result1: %d", result1);
      $display("result2: %d", result2);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
  always @(reset1) begin
    reset2 <= t.reset;
  end

  test_mod t (
    .clk(clk),
    .reset(reset1),
    .result(result1)
  );
  test_mod t2 (
    .clk(clk),
    .reset(reset2),
    .result(result2));
  endmodule

module Dut_wrapper(input clk);

  Dut d(.clk(clk));
  Dut d2(.clk(clk));
endmodule

module t (/*AUTOARG*/
   clk);
  input clk;
  Dut_wrapper d_w(.clk(clk));
endmodule
