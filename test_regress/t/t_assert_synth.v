// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg 	 a;	initial a = 1'b1;
   reg 	 b_fc;	initial b_fc = 1'b0;
   reg 	 b_pc;	initial b_pc = 1'b0;
   reg 	 b_oh;	initial b_oh = 1'b0;
   reg 	 b_oc;	initial b_oc = 1'b0;
   wire  a_l = ~a;
   wire  b_oc_l = ~b_oc;

   // Note we must insure that full, parallel, etc, only fire during
   // edges (not mid-cycle), and must provide a way to turn them off.
   // SystemVerilog provides:  $asserton and $assertoff.

   // verilator lint_off CASEINCOMPLETE

   always @* begin
      // Note not all tools support directives on casez's
      case ({a,b_fc}) // synopsys full_case
	2'b0_0: ;
	2'b0_1: ;
	2'b1_0: ;
	// Note no default
      endcase
      priority case ({a,b_fc})
	2'b0_0: ;
	2'b0_1: ;
	2'b1_0: ;
	// Note no default
      endcase
   end

   always @* begin
      case (1'b1) // synopsys full_case parallel_case
	a: ;
	b_pc: ;
      endcase
   end

`ifdef NOT_YET_VERILATOR // Unsupported
   // ambit synthesis one_hot "a, b_oh"
   // cadence one_cold "a_l, b_oc_l"
`endif

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    a <= 1'b1;
	    b_fc <= 1'b0;
	    b_pc <= 1'b0;
	    b_oh <= 1'b0;
	    b_oc <= 1'b0;
	 end
	 if (cyc==2) begin
	    a <= 1'b0;
	    b_fc <= 1'b1;
	    b_pc <= 1'b1;
	    b_oh <= 1'b1;
	    b_oc <= 1'b1;
	 end
	 if (cyc==3) begin
	    a <= 1'b1;
	    b_fc <= 1'b0;
	    b_pc <= 1'b0;
	    b_oh <= 1'b0;
	    b_oc <= 1'b0;
	 end
	 if (cyc==4) begin
`ifdef FAILING_FULL
	    b_fc <= 1'b1;
`endif
`ifdef FAILING_PARALLEL
	    b_pc <= 1'b1;
`endif
`ifdef FAILING_OH
	    b_oh <= 1'b1;
`endif
`ifdef FAILING_OC
	    b_oc <= 1'b1;
`endif
	 end
	 if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule
