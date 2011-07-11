// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   const logic [2:0] five = 3'd5;

   always @ (posedge clk) begin
      five = 3'd4;
      if (five !== 3'd5) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
