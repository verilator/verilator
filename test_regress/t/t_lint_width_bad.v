// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();

   // See also t_math_width

   // This shows the uglyness in width warnings across param modules
   // TODO: Would be nice to also show relevant parameter settings
   p #(.WIDTH(4)) p4 (.in(4'd0));
   p #(.WIDTH(5)) p5 (.in(5'd0));

   //====
   localparam [3:0]     XS = 'hx;  // User presumably intended to use 'x

   //====
   wire [4:0] c = 1'b1 << 2;  // No width warning, as is common syntax
   wire [4:0] d = (1'b1 << 2) + 5'b1;  // Has warning as not obvious what expression width is

   //====
   localparam           WIDTH = 6;
   wire                 one_bit;
   wire [2:0]           shifter = 1;
   wire [WIDTH-1:0]     masked = (({{(WIDTH){1'b0}}, one_bit}) << shifter);

   //====
   // We presently warn here, in theory we could detect if the number of one bit additions could overflow the LHS
   wire                 one = 1;
   wire [2:0]           cnt  = (one + one + one + one);

   // Not harmless > or >= compared with something wider (as different results if "a" wider)
   localparam [40:0] THREE = 3;
   int        a;
   initial for (a = 0; a > THREE; ++a) $display(a);
   initial for (a = 0; a >= THREE; ++a) $display(a);

   initial if (THREE) $stop;

endmodule

module p
  #(parameter WIDTH=64)
   (input [WIDTH-1:0] in);
   wire [4:0] out = in;
endmodule
