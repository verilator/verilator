// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

`verilator_config
profile_data -model "x" -mtask "h7baded98__0" -cost 64'd12345678901234567890
profile_data -model "x" -mtask "hb56134bd__0" -cost 945
