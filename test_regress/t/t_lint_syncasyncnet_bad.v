// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, rst_both_l, rst_sync_l, rst_async_l, d
   );
   /*AUTOINPUT*/

   input clk;
   input rst_both_l;
   input rst_sync_l;
   input rst_async_l;

   input d;
   reg q1;
   reg q2;

   always @(posedge clk) begin
      if (~rst_sync_l) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         q1 <= 1'h0;
         // End of automatics
      end else begin
         q1 <= d;
      end
   end

   always @(posedge clk) begin
      q2 <= (rst_both_l) ? d : 1'b0;
      if (0 && q1 && q2) ;
   end

   reg   q3;
   always @(posedge clk or negedge rst_async_l) begin
      if (~rst_async_l) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         q3 <= 1'h0;
         // End of automatics
      end else begin
         q3 <= d;
      end
   end

   reg q4;
   always @(posedge clk or negedge rst_both_l) begin
      q4 <= (~rst_both_l) ? 1'b0 : d;
   end
   // Make there be more async uses than sync uses
   reg q5;
   always @(posedge clk or negedge rst_both_l) begin
      q5 <= (~rst_both_l) ? 1'b0 : d;
      if (0 && q3 && q4 && q5) ;
   end

endmodule
