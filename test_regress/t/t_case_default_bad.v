// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   value
   );
   input [3:0] value;
   always @ (/*AS*/value) begin
      case (value)
        default: $stop;
        4'd0000: $stop;
        default: $stop;
      endcase
   end
endmodule
