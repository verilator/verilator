// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  reg [1:0] in;
  wire [2:0] out;

  // verilator lint_off WIDTH
  buf buf1 (out[0], 1);  // <--- BAD wrong connection width
  buf buf2[0:0] (out[1], 2'b01);  // <--- BAD wrong connection width
  buf buf3[0:0] (out[2], in[1:0]);  // <--- BAD wrong connection width
  buf buf4[3:0] (out[2], in[1:0]);  // <--- BAD wrong connection width

  initial $stop;

endmodule
