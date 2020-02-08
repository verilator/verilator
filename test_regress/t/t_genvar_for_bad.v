// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   ov,
   // Inputs
   clk, iv
   );

   parameter N = 4;

   input         clk;
   input [63:0]  iv[N-1:0];
   output logic [63:0] ov[N-1:0];

   genvar        i;
   generate
      always @(posedge clk) begin
         for (i=0; i<N; i=i+1) begin
            ov[i] <= iv[i];
         end
      end
   endgenerate
endmodule
