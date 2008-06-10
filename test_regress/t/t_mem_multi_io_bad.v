// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   dim1
   );
   reg [1:0] dim1 [1:0];
   output dim1;	// Bad, can't output multi-dim
endmodule

