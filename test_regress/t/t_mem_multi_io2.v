// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   o3, o34, o345,
   // Inputs
   i3, i34, i345
   );
   input  [15:0] i3;
   output wire [15:0] o3;
   input [15:0]       i34 [3:0];
   output wire [15:0] o34 [3:0];
   input [15:0]       i345 [3:0][4:0];
   output wire [15:0] o345 [3:0][4:0];

   sub sub (.*);
endmodule

module sub (/*AUTOARG*/
   // Outputs
   o3, o34, o345,
   // Inputs
   i3, i34, i345
   );
   input  [15:0] i3;
   output wire [15:0] o3;
   input [15:0]       i34 [3:0];
   output wire [15:0] o34 [3:0];
   input [15:0]       i345 [3:0][4:0];
   output wire [15:0] o345 [3:0][4:0];

   assign o3 = i3;
   assign o34 = i34;
   assign o345 = i345;

endmodule
