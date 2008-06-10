// -*- Verilog -*-
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.
//====================================================================

// Module gray2bin
// convert an arbitrary width gray coded number to binary. The conversion
// of a 4 bit gray (represented as "g") to binary ("b") would go as follows:
// b[3] = ^g[3] = g[3]
// b[2] = ^g[3:2]
// b[1] = ^g[3:1]
// b[0] = ^g[3:[SZ-1:0] 	cur0]

module t_func_grey2bin (/*AUTOARG*/
   // Outputs
   b,
   // Inputs
   g
   );

   // surefire lint_off STMFOR

   parameter SZ = 5;
   output [SZ-1:0] b;
   input [SZ-1:0]  g;

   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [SZ-1:0]		b;
   // End of automatics

   integer 	   i;
   always @(/*AUTOSENSE*/g)
     for (i=0; i<SZ; i=i+1)
       b[i] = ^(g >> i);  // surefire lint_off_line LATASS

endmodule
