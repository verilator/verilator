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

  initial begin
    n7 = -7'sd3;
    n72 = -72'sd3;
    #10;
    `checkh(out35, '0);
    `checkh(n7_32, 7'h7f);
    `checkh(n7_100, 7'h7f);
    `checkh(n72_100, 72'hff_ffffffff_ffffffff);
    `checkh(n72_200, 72'hff_ffffffff_ffffffff);
    n7 = 7'sd3;
    n72 = 72'sd3;
    #10;
    `checkh(n7_32, 7'h00);
    `checkh(n7_100, 7'h00);
    `checkh(n72_100, 72'h0);
    `checkh(n72_200, 72'h0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
