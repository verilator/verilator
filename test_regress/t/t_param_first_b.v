// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t_param_first_b (/*AUTOARG*/
   // Outputs
   par, varwidth
   );

   parameter X = 1;
   parameter FIVE = 0; // Overridden
   parameter TWO = 2;

   output [4:0] 	par;
   output [X:0] 	varwidth;

   wire [4:0]	par = X;
   wire [X:0] 	varwidth = (FIVE==5)?TWO:0;

endmodule
