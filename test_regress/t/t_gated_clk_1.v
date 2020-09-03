// DESCRIPTION: Verilator: Test of gated clock detection
//
// The code as shown generates a result by a delayed assignment from PC. The
// creation of the result is from a clock gated from the clock that sets
// PC. Howevever since they are essentially the same clock, the result should
// be delayed by one cycle.
//
// Standard Verilator treats them as different clocks, so the result stays in
// step with the PC. An event drive simulator always allows the clock to win.
//
// The problem is caused by the extra loop added by Verilator to the
// evaluation of all internally generated clocks (effectively removed by
// marking the clock enable).
//
// This test is added to facilitate experiments with solutions.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Jeremy Bennett <jeremy.bennett@embecosm.com>.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg gated_clk_en = 1'b0 ;
   reg [1:0] pc = 2'b0;
   reg [1:0] res = 2'b0;

   wire gated_clk = gated_clk_en & clk;

   always @(posedge clk) begin
      pc <= pc + 1;
      gated_clk_en <= 1'b1;
   end

   always @(posedge gated_clk) begin
      res <= pc;
   end

   always @(posedge clk) begin
      if (pc == 2'b11) begin
	 // Correct behaviour is that res should be lagging pc in the count
	 // by one cycle
	 if (res == 2'b10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
	 else begin
	   $stop;
	 end
      end
   end

endmodule
