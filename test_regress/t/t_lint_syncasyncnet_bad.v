// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   rst_sync_l, rst_both_l, rst_async_l, d, clk
   );
   /*AUTOINPUT*/
   // Beginning of automatic inputs (from unused autoinst inputs)
   input                clk;                    // To sub1 of sub1.v, ...
   input                d;                      // To sub1 of sub1.v, ...
   input                rst_async_l;            // To sub2 of sub2.v
   input                rst_both_l;             // To sub1 of sub1.v, ...
   input                rst_sync_l;             // To sub1 of sub1.v
   // End of automatics

   sub1 sub1 (/*AUTOINST*/
              // Inputs
              .clk                      (clk),
              .rst_both_l               (rst_both_l),
              .rst_sync_l               (rst_sync_l),
              .d                        (d));
   sub2 sub2 (/*AUTOINST*/
              // Inputs
              .clk                      (clk),
              .rst_both_l               (rst_both_l),
              .rst_async_l              (rst_async_l),
              .d                        (d));
endmodule

module sub1 (/*AUTOARG*/
   // Inputs
   clk, rst_both_l, rst_sync_l, d
   );

   input clk;
   input rst_both_l;
   input rst_sync_l;
   //input rst_async_l;
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

endmodule

module sub2 (/*AUTOARG*/
   // Inputs
   clk, rst_both_l, rst_async_l, d
   );

   input clk;
   input rst_both_l;
   //input rst_sync_l;
   input rst_async_l;
   input d;
   reg   q1;
   reg   q2;
   reg   q3;

   always @(posedge clk or negedge rst_async_l) begin
      if (~rst_async_l) begin
         /*AUTORESET*/
         // Beginning of autoreset for uninitialized flops
         q1 <= 1'h0;
         // End of automatics
      end else begin
         q1 <= d;
      end
   end

   always @(posedge clk or negedge rst_both_l) begin
      q2 <= (~rst_both_l) ? 1'b0 : d;
   end
   // Make there be more async uses than sync uses
   always @(posedge clk or negedge rst_both_l) begin
      q3 <= (~rst_both_l) ? 1'b0 : d;
      if (0 && q1 && q2 && q3) ;
   end

endmodule
