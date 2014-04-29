// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   passed,
   // Inputs
   clk, fastclk, reset_l
   );

   input clk /*verilator sc_clock*/;
   input fastclk /*verilator sc_clock*/;
   input reset_l;
   output passed;

   reg [31:0] count_c;
   reg [31:0] count_f;

   always @ (posedge clk) begin
      if (!reset_l) begin
	 /*AUTORESET*/
	 // Beginning of autoreset for uninitialized flops
	 count_c <= 32'h0;
	 // End of automatics
      end else begin
	 count_c <= count_c + 1;
      end
   end

   always @ (posedge fastclk) begin
      if (!reset_l) begin
	 /*AUTORESET*/
	 // Beginning of autoreset for uninitialized flops
	 count_f <= 32'h0;
	 passed <= 1'h0;
	 // End of automatics
      end else begin
	 count_f <= count_f + 1;
	 if (count_f == 5) passed <= 1'b1;
      end
   end

endmodule
