// DESCRIPTION: Verilator: Simple test of CLkDATA
//
// Trigger the CLKDATA detection
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Jie Xu.

localparam ID_MSB = 1;


module t (/*AUTOARG*/
   // Inputs
   clk,
   res,
   res8,
   res16
   );
   input clk;
   output        res;
   output [7:0]  res8;
   output [15:0] res16;


   wire [7:0] clkSet;
   wire       clk_1;
   wire [2:0] clk_3;
   wire [3:0] clk_4;
   wire       clk_final;
   reg  [7:0] count;


   assign clkSet = {8{clk}};
   assign clk_4 = clkSet[7:4];
   assign clk_1 = clk_4[0];;

   // arraysel
   assign clk_3 = {3{clk_1}};
   assign clk_final = clk_3[0];

   // the following two assignment triggers the CLKDATA warning
   // because on LHS there are a mix of signals both CLOCK and 
   // DATA
   /* verilator lint_off CLKDATA */
   assign res8  = {clk_3, 1'b0, clk_4};
   assign res16 = {count, clk_3, clk_1, clk_4};
   /* verilator lint_on CLKDATA */


   initial 
       count = 0;


   always @(posedge clk_final or negedge clk_final) begin
       count = count + 1;
       // the following assignment should trigger the CLKDATA warning
       // because CLOCK signal is used as DATA in sequential block
       /* verilator lint_off CLKDATA */
       res <= clk_final;
       /* verilator lint_on CLKDATA */
      if ( count == 8'hf) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
