// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg 	 sync_blk;
   reg 	 sync_nblk;
   reg 	 combo_blk;
   reg 	 combo_nblk;

   always @(posedge clk) begin
      sync_blk = 1'b1; 
      sync_nblk <= 1'b1; 
   end

   always @* begin
      combo_blk = 1'b1; 
      combo_nblk <= 1'b1; 
   end

endmodule

