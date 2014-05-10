// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

module t ();

   // See also t_lint_width

   b #(.B_WIDTH(48)) b ();

   reg [4:0] c;
   integer    c_i;
   initial begin
      c_i = 3;
      c = 1'b1 << c_i;  // No width warning when not embedded in expression, as is common syntax
      if (c != 5'b1000) $stop;
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
