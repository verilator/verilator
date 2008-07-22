// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005-2007 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   value
   );

   input [3:0] value;
   always @ (/*AS*/value) begin
      casez (value)
	4'b0000: $stop;
	4'b1xxx: $stop;
	default: $stop;
      endcase
   end

endmodule
