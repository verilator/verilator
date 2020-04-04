// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

module top (input A, input OE, output X, output Y, output Z);

   pullup p1(Z);
   assign Z = OE ? A : 1'bz;

   pulldown p2(Y);
   assign Y = OE ? A : 1'bz;

   pass pass(.A(A), .OE(OE), .X(X));
   pullup_module p(X);
endmodule

module pass (input A, input OE, inout X);
   io io(.A(A), .OE(OE), .X(X));
endmodule

module io (input A, input OE, inout X);
   assign X = (OE) ? A : 1'bz;
endmodule

module pullup_module (output X);
   pullup p1(X);
endmodule
