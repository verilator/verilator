// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   rc, rg, ri, rp, rw
   );

   parameter P = 17;
   wire [4:0] w = 5'd1;

   output reg [3:0] rc;
   output reg [3:0] rg;
   output reg [3:0] ri;
   output reg [3:0] rp;

   output reg [3:0] rw;

   for (genvar g=16; g < 17; ++g) begin
      // Index 17 makes a width violation
      initial begin
         rg = g;  // WidthMin mismatch
         rp = P;  // WidthMin mismatch
         rw = w;  // Always a mismatch
         rc = 64'h1;  // Always a mismatch (as sized)
      end
   end
   initial begin
      for (integer i=16; i < 17; ++i) begin
         ri = i;  // WidthMin mismatch
      end
   end

endmodule
