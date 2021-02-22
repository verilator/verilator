// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 Wilson Snyder and Marlon James.
// SPDX-License-Identifier: CC0-1.0


module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   int   count;

   always @(posedge clk) begin
      count <= count + 1;
      if (count == 10) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
   end

endmodule : t
