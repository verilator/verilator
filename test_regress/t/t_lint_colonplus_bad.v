// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   z
   );

   reg [3:0] r = 4'b1010;
   output [2:1] z = r[2 :+ 1];

endmodule
