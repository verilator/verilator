// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   outwires,
   // Inputs
   inwires
   );
   input [7:0] inwires [12:10];
   output wire [7:0] outwires [12:10];

   assign outwires[10] = inwires[11];
   assign outwires[11] = inwires[12];
   assign outwires[12] = inwires[13];	// must be an error here

endmodule
