// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc=1;
   integer a, b, c, d, e, f, g, h, i, j, k, l;

   always @ (posedge clk) begin
      cyc <= cyc + 1;

      //====================
      // Positive test cases
      //====================

      // Single if, which is untrue sometimes
      unique0 if (cyc > 5)
	a <= 17;

      // single if with else
      unique0 if (cyc < 3)
	b <= 17;
      else
	b <= 19;

      // multi if, some cases may not be true
      unique0 if (cyc < 3)
	c <= 17;
      else if (cyc > 3)
	c <= 19;

      // multi if with else, else clause hit in some cases
      unique0 if (cyc < 3)
	d <= 17;
      else if (cyc > 3)
	d <= 19;
      else
	d <= 21;

      // single if with else
      unique if (cyc < 3)
	f <= 17;
      else
	f <= 19;

      // multi if
      unique if (cyc < 3)
	g <= 17;
      else if (cyc >= 3)
	g <= 19;

      // multi if with else, else clause hit in some cases
      unique if (cyc < 3)
	h <= 17;
      else if (cyc > 3)
	h <= 19;
      else
	h <= 21;

      //====================
      // Negative test cases
      //====================
`ifdef FAILING_ASSERTION1
      $display("testing fail 1: %d", cyc);
      // multi if, multiple cases true
      unique0 if (cyc < 3)
	i <= 17;
      else if (cyc < 5)
	i <= 19;
`endif

`ifdef FAILING_ASSERTION2
      // multi if, multiple cases true
      unique if (cyc < 3)
	j <= 17;
      else if (cyc < 5)
	j <= 19;
`endif

`ifdef FAILING_ASSERTION3
      // multi if, no cases true
      unique if (cyc > 1000)
	k <= 17;
      else if (cyc > 2000)
	k <= 19;
`endif

`ifdef FAILING_ASSERTION4
      // Single if, which is untrue sometimes.
      // The LRM states: "A software tool shall also issue an error if it determines that no condition'
      // is true, or it is possible that no condition is true, and the final if does not have a
      // corresponding else."  In this case, the final if is the only if, but I think the clause
      // still applies.
      unique if (cyc > 5)
	l <= 17;
`endif


      if (cyc==10) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule
