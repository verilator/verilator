// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg  [7:0] x;
   wire [3:0] en;
   wire       sel;
   wire       a;
   
   // bug675
   generate
      genvar  g_k;
      for ( g_k = 0; g_k < 8; g_k = g_k + 1 )
        begin: g_index
	   always @* begin
	      // Note this isn't a genif, but normal if
	      // verilator lint_off SELRANGE
	      if(g_k<4) begin
                 x[g_k] = (sel == 1'b1) ? 1'b1 : (en[g_k] == 1'b0) ? 1'b1 : a;
              end
	      else begin
                 x[g_k] = (sel == 1'b0) ? 1'b1 : (en[g_k-4] == 1'b0) ? 1'b1 : a;
              end
	      // verilator lint_on SELRANGE
           end
        end
   endgenerate
   
endmodule
