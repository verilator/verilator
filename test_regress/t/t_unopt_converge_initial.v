// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   x,
   // Inputs
   clk
   );

`ifdef ALLOW_UNOPT
   /*verilator lint_off UNOPTFLAT*/
`endif

   input clk;
   output [31:0] x;  // Avoid eliminating x

   reg [31:0] x;
   always @* begin
      x = x ^ $random;
   end

endmodule
