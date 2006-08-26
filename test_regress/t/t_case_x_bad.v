// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005-2006 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   value
   );

   input [3:0] value;
   always @ (/*AS*/value) begin
      case (value)
	4'b0000: $stop;
	4'b1xxx: $stop;
	default: $stop;
      endcase
   end

endmodule
