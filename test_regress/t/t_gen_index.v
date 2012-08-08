// DESCRIPTION: Verilator: Test generate index usage.
//
// The code illustrates a problem in Verilator's handling of constant
// expressions inside generate indexes.
//
// This is a regression test against issue 517.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.


`define START 8
`define SIZE  4
`define END   (`START + `SIZE)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [`END-1:0]   y;
   wire [`END-1:0]  x;

   foo foo_i (.y   (y),
	      .x   (x),
	      .clk (clk));

   always @(posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule // t


module foo(output wire [`END-1:0] y,
	   input wire [`END-1:0] x,
	   input wire 		 clk);

   function peek_bar;
      peek_bar = bar_inst[`START].i_bar.r;       // this is ok
      peek_bar = bar_inst[`START + 1].i_bar.r;   // this fails, should not.
   endfunction

   genvar g;
   generate
      for (g = `START; g < `END; g = g + 1) begin: bar_inst
         bar i_bar(.x   (x[g]),
		   .y   (y[g]),
		   .clk (clk));
      end
   endgenerate

endmodule : foo


module bar(output wire y,
	   input wire x,
	   input wire clk);

   reg r = 0;
   assign y = r;

   always @(posedge clk) begin
      r = x ? ~x : y;
   end

endmodule : bar
