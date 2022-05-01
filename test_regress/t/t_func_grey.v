// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   // surefire lint_off _NETNM
   // surefire lint_off STMINI

   input clk;
   integer _mode;   initial _mode = 0;

   wire [2:0] b3; reg [2:0] g3;
   wire [5:0] b6; reg [5:0] g6;

   t_func_grey2bin #(3) g2b3 (.b(b3), .g(g3));
   t_func_grey2bin #(6) g2b6 (.b(b6), .g(g6));

   always @ (posedge clk) begin
      if (_mode==0) begin
         _mode <= 1;
         g3 <= 3'b101;
         g6 <= 6'b110101;
      end
      else if (_mode==1) begin
         if (b3 !== 3'b110) $stop;
         if (b6 !== 6'b100110) $stop;
         _mode <= 2;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

// Module gray2bin
// convert an arbitrary width gray coded number to binary. The conversion
// of a 4 bit gray (represented as "g") to binary ("b") would go as follows:
// b[3] = ^g[3] = g[3]
// b[2] = ^g[3:2]
// b[1] = ^g[3:1]
// b[0] = ^g[3:[SZ-1:0]         cur0]

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
   reg [SZ-1:0]         b;
   // End of automatics

   integer         i;
   always @(/*AUTOSENSE*/g)
     for (i=0; i<SZ; i=i+1)
       b[i] = ^(g >> i);  // surefire lint_off_line LATASS

endmodule
