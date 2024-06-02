// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jonathon Donaldson.
// SPDX-License-Identifier: CC0-1.0

module t
  (
   input        i_clk,
   input [6:0]  i_input,
   output logic o_output
   );

   always_ff @(posedge i_clk)
     // verilator lint_off CASEINCOMPLETE
     case (i_input)
       7'(92+2),
       7'(92+3): o_output <= 1'b1;
     endcase

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
