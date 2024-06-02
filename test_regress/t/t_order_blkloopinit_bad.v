// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off MULTIDRIVEN

module t (/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   clk
   );
   input clk;
   output int o;

   localparam SIZE = 65536;

   // Unsupported case 1: Array NBA inside suspendable
   int array1 [SIZE];
   always @ (posedge clk) begin
      #1;
      o <= array1[1];
      for (int i=0; i<SIZE; i++) begin
         array1[i] <= 0;  // BLKLOOPINIT
      end
   end

   // Unsupported case 2: Array NBA to compund type
   class C; endclass
   C array2[SIZE];
   always @ (negedge clk) begin
      o <= int'(array2[1] == null);
      for (int i=0; i<SIZE; i++) begin
         array2[i] <= null;  // BLKLOOPINIT
      end
   end

   // Unsupported case 3: Array NBA to array also assigned in suspendable
   int array3 [SIZE];
   always @ (posedge clk) begin
      o <= array3[1];
      for (int i=0; i<SIZE; i++) begin
         array3[i] <= 0;  // BLKLOOPINIT
      end
   end

   always @(posedge clk) begin
      #1 array3[0] <= 0;
   end

endmodule
