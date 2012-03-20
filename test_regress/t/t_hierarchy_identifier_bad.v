// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   parameter SIZE = 8;

   integer cnt = 0;

   logic [SIZE-1:0] vld_for;
   logic            vld_if   = 1'b0;
   logic            vld_else = 1'b0;

   genvar i;

   // event counter
   always @ (posedge clk) begin
      cnt <= cnt + 1;
   end

   // finish report
   always @ (posedge clk)
   if (cnt==SIZE) begin : if_cnt_finish
      $write("*-* All Finished *-*\n");
      $finish;
   end : if_cnt_finish_bad

   generate
   for (i=0; i<SIZE; i=i+1) begin : generate_for
      always @ (posedge clk)
      if (cnt == i)  vld_for[i] <= 1'b1;
   end : generate_for_bad
   endgenerate

   generate
   if (SIZE>0) begin : generate_if_if
      always @ (posedge clk)
      vld_if <= 1'b1;
   end : generate_if_if_bad
   else begin : generate_if_else
      always @ (posedge clk)
      vld_else <= 1'b1;
   end : generate_if_else_bad
   endgenerate

endmodule : t_bad
