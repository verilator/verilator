// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define WIDTH 8192

module WideOps(
  input          clk,
                 reset,
  input  [2:0]   in,
  output [`WIDTH:0] out
);

  reg  [`WIDTH:0]      test_0;
  reg  [`WIDTH:0]      test_1;
  wire [1:0][`WIDTH:0] wide_array_0 =
    {{test_1}, {test_0}};

  reg  [`WIDTH:0]      test_4;
  reg  [`WIDTH:0]      test_5;
  wire [1:0][`WIDTH:0] wide_array_1 =
    {{test_5}, {test_4}};

  always @(posedge clk) begin
    if (reset) begin
      test_0 <= 1;
      test_1 <= 1;
      test_4 <= 1;
      test_5 <= 1;
    end
    else begin
      test_0 <= {test_0[`WIDTH:3], test_0[2:0] ^ in};
      test_1 <= {test_1[`WIDTH:3], test_1[2:0] ^ in};

      test_4 <= {test_4[`WIDTH:3], test_4[2:0] ^ in};
      test_5 <= {test_5[`WIDTH:3], test_5[2:0] ^ in};
    end
  end
  assign out = wide_array_0[in] ^ wide_array_1[in][`WIDTH:0];
endmodule

module t(/*AUTOARG*/
    // Inputs
    clk, reset
  );
  input clk;
  input reset;

  reg [2:0] in = 3'b111;
  reg [`WIDTH:0] out;
  WideOps x(.clk(clk), .reset(reset), .in(in), .out(out));
  initial begin
    if (out === 0) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $stop;
    end
  end
endmodule
