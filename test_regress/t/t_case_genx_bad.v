// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005-2007 by Wilson Snyder.

module t (/*AUTOARG*/);

   parameter P = 32'b1000;

   generate
      case (P)
	32'b0:    initial begin end
	32'b1xxx: initial begin end
	default:  initial begin end
      endcase
   endgenerate

endmodule
