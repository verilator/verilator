// DESCRIPTION: Verilator: Verilog Test module
//
// We see Verilator assumes a 1-bit parameter is a scalar rather than a 1-bit
// long vector. This causes the following code to fail.
//
// Other event drive simulators accept this.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Jeremy Bennett
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // At this point it is ambiguous whether a is scalar or vector
   parameter A = 1'b0;
   wire  b = A[0];
   // Note however b[0] is illegal.

   always @(posedge clk) begin
      if (b == 1'b0) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $stop;
      end
   end

endmodule
