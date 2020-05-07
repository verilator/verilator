// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2015 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

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
   assign outwires[12] = inwires[13];  // must be an error here

endmodule
