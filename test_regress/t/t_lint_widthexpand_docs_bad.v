// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [31:0] array[5];
  bit [1:0] rd_addr;
  wire [31:0] rd_value = array[rd_addr];  //<--- Warning

  ok ok ();
endmodule

module ok;
  logic [31:0] array[5];
  bit [1:0] rd_addr;
  wire [31:0] rd_value = array[{1'b0, rd_addr}];  //<--- Fixed
endmodule
