// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t
   (
   output wire o,
   input wire i,
   input wire i2
   );

   sub
     #(, .P(2), .P(3))
   sub (.o(o),
	.i(i),
	.i(i2),
	);

endmodule

module sub
  #(parameter P=1)
  (
   output wire o,
   input wire i
   );

   assign o = ~i;

endmodule
