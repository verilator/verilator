// DESCRIPTION: Verilator: Non-cutable edge in loop
//
// This code (stripped down from a much larger application) has a loop between
// the use of ready in the first two always blocks. However it should
// trivially trigger the $write on the first clk posedge.
//
// This is a regression test against issue 513.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg   ready;

   initial begin
      ready = 1'b0;
   end

   always @(posedge ready) begin
      if ((ready === 1'b1)) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   always @(posedge ready) begin
      if ((ready === 1'b0)) begin
         ready = 1'b1 ;
      end
   end

   always @(posedge clk) begin
      ready = 1'b1;
   end

endmodule
