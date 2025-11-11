// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   nnext,
   // Inputs
   inibble, onibble
   );

   input [3:0]      inibble;
   input [106:0]    onibble;

   output reg [3:0] nnext [0:7];

   // verilator lint_off WIDTH
   wire [2:0]       selline = (onibble >>> 102) & 7;
   // verilator lint_on WIDTH

   always_comb begin
      for (integer i=0; i<8; i=i+1) begin
         nnext[i] = '0;
      end
      nnext[selline] = inibble;
   end

endmodule
