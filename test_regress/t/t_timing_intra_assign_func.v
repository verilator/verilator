// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  reg [3:0] ia = 4'd1;
  wire signed [3:0] iufunc;

  // verilator lint_off WIDTH
  assign #1 iufunc = int_func(ia);
  // verilator lint_on WIDTH

  function [31:0] int_func;
    input [31:0] in;
    int_func = in * 2;
  endfunction

  initial begin
      #1
      if (iufunc != 4'd2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
  end
endmodule
