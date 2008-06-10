// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

// This file has DOS carrage returns in it!
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
// This file has DOS carrage returns in it!
