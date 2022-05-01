// DESCRIPTION: Verilator: Simple test of unoptflat
//
// Trigger the DETECTARRAY error on packed structure.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jie Xu.
// SPDX-License-Identifier: CC0-1.0

localparam ID_MSB = 1;


module t (/*AUTOARG*/
   // Inputs
   clk,
   res
   );
   input clk;
   output [8:0][8:0] res;

   logic a = 1'b1;
   logic [8:0] b [8:0];  // where the error is reported
   logic [8:0][8:0] c;  // where the error is reported

   // following just to make c as circular
   assign c[0] = c[0] | a << 1;
   assign b[0] = b[0] | a << 2;

   assign res[0] = c[0];
   assign res[1] = b[0];


   always @(posedge clk or negedge clk) begin

     if (res != 0) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
