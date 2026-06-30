// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
  logic [3:0] zero4 = 4'b0;
  logic [3:0] small4 = 4'b0010;
  logic [7:0] small8 = 8'h01;
  logic [15:0] msb16 = 16'h8000;
  int sig;
  logic [31:0] mid32 = 32'h0000_00a5;
  logic [63:0] msb64 = 64'h8000_0000_0000_0000;
  logic [99:0] wide_skip = 100'h1_0000_0000;
  logic [67:0] wide_partial = 68'h2_0000_0000_0000_0000;

  initial begin
    sig = 10;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
    #20;
    sig = 20;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
