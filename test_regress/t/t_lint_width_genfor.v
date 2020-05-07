// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   rc, rg, ri, rp
   );

   parameter P = 15;

   output reg [3:0] rc;
   output reg [3:0] rg;
   output reg [3:0] ri;
   output reg [3:0] rp;

   for (genvar g=0; g < 15; ++g) begin
      // bug1487
      // This isn't a width violation, as genvars are generally 32 bits
      initial begin
         rg = g;
         rp = P;
         rc = 1;
      end
   end
   initial begin
      for (integer i=0; i < 15; ++i) begin
         /* verilator lint_off WIDTH */
         ri = i;
         /* verilator lint_on WIDTH */
      end
   end

endmodule
