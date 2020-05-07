// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug477

module t (
          input  rst_n,
          input  clk,
          output out
          );

   submod #(.STAGES(5)) u2(.*);

endmodule

module submod (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   rst_n, clk
   );

   parameter STAGES = 4;

   input   rst_n;
   input   clk;
   output  out;

   reg [STAGES-1:0] r_rst;

   generate
      // for i=0..5  (5+1-1)
      for (genvar i=0; i<STAGES+1-1; i=i+1) begin
         always @(posedge clk or negedge rst_n) begin
            if (~rst_n)
              r_rst[i] <= 1'b0;
            else begin
               if (i==0)
                 r_rst[i] <= 1'b1;
               else
                 r_rst[i] <= r_rst[i-1];  // i=0, so -1 wraps to 7
            end
         end
      end
   endgenerate

   wire out = r_rst[STAGES-1];

endmodule
