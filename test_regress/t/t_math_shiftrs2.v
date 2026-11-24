// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module top (
    out35
);
  output wire [2:0] out35;
  wire signed [2:0] wire_4;
  assign wire_4 = 3'b011;
  assign out35 = (wire_4 >>> 36'hffff_ffff_f);

  // Constant shift >= the width must fill with the sign bit
  logic signed [6:0] n7;
  logic signed [71:0] n72;
  wire signed [6:0] n7_32 = n7 >>> 32;
  wire signed [6:0] n7_100 = n7 >>> 100;
  wire signed [71:0] n72_100 = n72 >>> 100;
  wire signed [71:0] n72_200 = n72 >>> 200;

  // Expression operand with width % 32 == 1
  logic signed [64:0] a65;
  logic signed [64:0] b65;
  logic signed [96:0] a97;
  logic signed [96:0] b97;
  wire signed [64:0] e65 = (a65 + b65) >>> 130;
  wire signed [96:0] e97 = (a97 + b97) >>> 130;
  logic signed [32:0] a33;
  logic signed [32:0] b33;
  logic signed [128:0] a129;
  logic signed [128:0] b129;
  wire signed [32:0] e33 = (a33 + b33) >>> 64;
  wire signed [128:0] e129 = (a129 + b129) >>> 200;

  initial begin
    n7 = -7'sd3;
    n72 = -72'sd3;
    a65 = -65'sd3;
    b65 = 65'sd2;
    a97 = -97'sd3;
    b97 = 97'sd2;
    a33 = -33'sd3;
    b33 = 33'sd2;
    a129 = -129'sd3;
    b129 = 129'sd2;
    #10;
    `checkh(e33, 33'h1_ffffffff);
    `checkh(e129, 129'h1_ffffffff_ffffffff_ffffffff_ffffffff);
    `checkh(e65, 65'h1_ffffffff_ffffffff);
    `checkh(e97, 97'h1_ffffffff_ffffffff_ffffffff);
    `checkh(out35, '0);
    `checkh(n7_32, 7'h7f);
    `checkh(n7_100, 7'h7f);
    `checkh(n72_100, 72'hff_ffffffff_ffffffff);
    `checkh(n72_200, 72'hff_ffffffff_ffffffff);
    n7 = 7'sd3;
    n72 = 72'sd3;
    a65 = 65'sd3;
    a97 = 97'sd3;
    a33 = 33'sd3;
    a129 = 129'sd3;
    #10;
    `checkh(e33, 33'h0);
    `checkh(e129, 129'h0);
    `checkh(e65, 65'h0);
    `checkh(e97, 97'h0);
    `checkh(n7_32, 7'h00);
    `checkh(n7_100, 7'h00);
    `checkh(n72_100, 72'h0);
    `checkh(n72_200, 72'h0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
