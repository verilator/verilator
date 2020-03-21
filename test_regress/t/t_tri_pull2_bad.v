// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   wire  A;

   pullup p1(A);

   child child(/*AUTOINST*/
	       // Inouts
	       .A			(A));

endmodule

module child(inout A);

   pulldown p2(A);

endmodule
