// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Wilson Snyder.

module t
   (
   input wire clk,
   input wire a
   );

   integer q;
   
   always @ (a or posedge clk)
     begin
	if (a)
          q = 0;
	else 
          q = q + 1;
     end

endmodule
