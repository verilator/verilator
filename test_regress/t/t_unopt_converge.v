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
   output x;   // Avoid eliminating x

   reg x;
   always @* begin
      x = ~x;
   end

endmodule
