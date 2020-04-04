// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   value
   );
   input [1:0] value;

   sub #(.CASEVAL(2'h0)) p0 (.value);
   sub #(.CASEVAL(2'h1)) p1 (.value);
   sub #(.CASEVAL(2'h2)) p2 (.value);
   sub #(.CASEVAL(2'h3)) p3 (.value);

endmodule

module sub
  (
   input [1:0] value);

   parameter [1:0] CASEVAL = 2'h0;
   always_comb begin
      case (value)
        CASEVAL: ;
        2'h2: $stop;
        default: ;
      endcase
   end
endmodule
