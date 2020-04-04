// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

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
