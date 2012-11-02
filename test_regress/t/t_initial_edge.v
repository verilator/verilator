// DESCRIPTION: Verilator: initial edge issue
//
// The module initial_edge drives the output "res" high when the reset signal,
// rst, goes high.
//
// The module initial_edge_n drives the output "res_n" high when the reset
// signal, rst_n, goes low.
//
// For 4-state simulators, that edge occurs when the initial value of rst_n,
// X, goes to zero. However, by default for Verilator, being 2-state, the
// initial value is zero, so no edge is seen.
//
// This is not a bug in verilator (it is bad design to rely on an edge
// transition from an unitialized signal), but the problem is that there are
// quite a few instances of code out there that seems to be dependent on this
// behaviour to get out of reset.
//
// The Verilator --x-initial-edge flag causes these initial edges to trigger,
// thus matching the behaviour of a 4-state simulator. This is reportedly also
// the behaviour of commercial cycle accurate modelling tools as well.
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty, 2012 by Wilson Snyder.

`timescale 1ns/1ns

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire  res;
   wire  res_n;
   reg 	 rst;
   reg 	 rst_n;

   integer count = 0;

   initial_edge i_edge (.res (res),
			.rst (rst));

   initial_edge_n i_edge_n (.res_n (res_n),
			    .rst_n (rst_n));

   // run for 3 cycles, with one cycle of reset.
   always @(posedge clk) begin

      rst   <= (count == 0) ? 1 : 0;
      rst_n <= (count == 0) ? 0 : 1;

      if (count == 3) begin
	 if ((res == 1) && (res_n == 1)) begin
	    $write ("*-* All Finished *-*\n");
	    $finish;
	 end
	 else begin
`ifdef TEST_VERBOSE
	    $write ("FAILED: res = %b, res_n = %b\n", res, res_n);
`endif
	    $stop;
	 end
      end

      count = count + 1;

   end

endmodule


module initial_edge_n (res_n,
		       rst_n);
   output  res_n;
   input   rst_n;

   reg 	   res_n = 1'b0;

   always @(negedge rst_n) begin
      if (rst_n == 1'b0) begin
         res_n <= 1'b1;
      end
   end

endmodule // initial_edge_n


module initial_edge (res,
		     rst);
   output  res;
   input   rst;

   reg 	   res = 1'b0;

   always @(posedge rst) begin
      if (rst == 1'b1) begin
         res <= 1'b1;
      end
   end

endmodule // initial_edge
