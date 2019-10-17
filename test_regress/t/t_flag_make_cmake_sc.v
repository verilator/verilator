// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
