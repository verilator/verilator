// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg 	 toggle;

   integer cyc; initial cyc=1;
   wire [7:0] cyc_copy = cyc[7:0];

   // psl cover  {cyc==3 || cyc==4} @ (posedge clk);
   // psl assert {cyc<100} @ (posedge clk) report "AssertionFalse1";
`ifdef FAILING_ASSERTIONS
   // psl assert {toggle} @ (posedge clk) report "AssertionShouldFail";
`endif

   // psl default clock = negedge clk;
//FIX   // psl assert always {cyc<99};
   // psl cover {cyc==9} report "DefaultClock,expect=1";

   // psl assert {(cyc==5)->toggle};
   // psl cover  {(cyc==5)->toggle} report "ToggleLogIf,expect=1";
`ifdef NOT_SUP
   // psl assert {toggle<->cyc[0]};
   // psl cover  {toggle<->cyc[0]} report "CycsLogIff,expect=10";
`endif
   
   // Test {{..}} == Sequence of sequence...
   // psl assert {{true}};

   always @ (negedge clk) begin
      //if (!(cyc==5) || toggle) $write("%d: %s\n", cyc, "ToggleLogIf,expect=1");
      //if (toggle&&cyc[0] || ~toggle&&~cyc[0]) $write("%d: %s\n", cyc, "CycsLogIff,expect=10");
   end

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 toggle <= !cyc[0];
	 if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule
