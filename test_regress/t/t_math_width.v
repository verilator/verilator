// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();

   // See also t_lint_width

   parameter A_ONE = '1;
   // verilator lint_off WIDTH
   parameter [3:0] A_W4 = A_ONE;
   // verilator lint_on WIDTH
   initial begin
      if ($bits(A_ONE) != 1 || A_ONE !== 1'b1) $stop;
      if ($bits(A_W4) != 4) $stop;
      if (A_W4 != 4'b0001) $stop;
   end

   b #(.B_WIDTH(48)) b ();

   reg [4:0] c;
   integer    c_i;
   initial begin
      c_i = 3;
      c = 1'b1 << c_i;  // No width warning when not embedded in expression, as is common syntax
      if (c != 5'b1000) $stop;
   end

   localparam D_TT = 32'd23;
   localparam D_SIX = 6;
   // verilator lint_off WIDTH
   localparam [5:0] D_SUB = D_TT - D_SIX;
   // verilator lint_on WIDTH
   initial begin
      if (D_SUB != 17) $stop;
   end

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule


module b;
   parameter B_WIDTH = 1;
   localparam B_VALUE0 = {B_WIDTH{1'b0}};
   localparam B_VALUE1 = {B_WIDTH{1'b1}};
   reg [47:0] b_val;
   initial begin
      b_val = B_VALUE0;
      if (b_val != 48'b0) $stop;
      b_val = B_VALUE1;
      if (b_val != ~48'b0) $stop;
   end
endmodule
