// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t (
`ifdef T_CLK_2IN_VEC
	  input [1:0] clks,
`else
	  input       c0,
	  input       c1,
`endif
	  input check
   );

`ifdef T_CLK_2IN_VEC
   wire    c0 = clks[0];
   wire    c1 = clks[1];
`endif

   integer p0 = 0;
   integer p1 = 0;
   integer p01 = 0;
   integer n0 = 0;
   integer n1 = 0;
   integer n01 = 0;

`define display_counts(text) begin \
   $write("[%0t] ",$time); \
   `ifdef T_CLK_2IN_VEC $write(" 2v "); `endif \
   $write(text); \
   $write(": %0d %0d %0d %0d %0d %0d\n",  p0, p1, p01, n0, n1, n01); \
   end

   always @ (posedge c0) begin
      p0 = p0 + 1;  // Want blocking, so don't miss clock counts
`ifdef TEST_VERBOSE `display_counts("posedge 0"); `endif
   end
   always @ (posedge c1) begin
      p1 = p1 + 1;
`ifdef TEST_VERBOSE `display_counts("posedge 1"); `endif
   end
   always @ (posedge c0 or posedge c1) begin
      p01 = p01 + 1;
`ifdef TEST_VERBOSE `display_counts("posedge *"); `endif
   end
   always @ (negedge c0) begin
      n0 = n0 + 1;
`ifdef TEST_VERBOSE `display_counts("negedge 0"); `endif
   end
   always @ (negedge c1) begin
      n1 = n1 + 1;
`ifdef TEST_VERBOSE `display_counts("negedge 1"); `endif
   end
   always @ (negedge c0 or negedge c1) begin
      n01 = n01 + 1;
`ifdef TEST_VERBOSE `display_counts("negedge *"); `endif
   end

   always @ (posedge check) begin
      if (p0!=4) $stop;
      if (p1!=4) $stop;
      if (p01!=6) $stop;
      if (n0!=4) $stop;
      if (n1!=4) $stop;
      if (n01!=6) $stop;
      $write("*-* All Finished *-*\n");
   end

endmodule
