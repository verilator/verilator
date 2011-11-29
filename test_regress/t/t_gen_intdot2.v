// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003-2007 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   integer 	cyc=0;

   reg 		check;
   initial check = 1'b0;
   Genit g (.clk(clk), .check(check));

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d %x %x\n",$time, cyc, check, out);
      cyc <= cyc + 1;
      if (cyc==0) begin
	 // Setup
	 check <= 1'b0;
      end
      else if (cyc==1) begin
	 check <= 1'b1;
      end
      else if (cyc==9) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

//`define WAVES
`ifdef WAVES
   initial begin
      $dumpfile("obj_dir/t_gen_intdot2/t_gen_intdot.vcd");
      $dumpvars(12, t);
   end
`endif

endmodule

module One;
   wire one = 1'b1;
endmodule

module Genit (
    input clk,
    input check);

   // ARRAY
   One cellarray1[1:0] ();	//cellarray[0..1][0..1]
   always @ (posedge clk) if (cellarray1[0].one !== 1'b1) $stop;
   always @ (posedge clk) if (cellarray1[1].one !== 1'b1) $stop;

   // IF
   generate
      // genblk1 refers to the if's name, not the "generate" itself.
      if (1'b1) // IMPLIED begin: genblk1
	One ifcell1(); // genblk1.ifcell1
      else
	One ifcell1(); // genblk1.ifcell1
   endgenerate
   // On compliant simulators "Implicit name" not allowed here; IE we can't use "genblk1" etc
`ifdef verilator
   always @ (posedge clk) if (genblk1.ifcell1.one !== 1'b1) $stop;
//`else // NOT SUPPORTED accoring to spec - generic block references
`endif

   generate
      begin : namedif2
	 if (1'b1)
	   One ifcell2();   // namedif2.genblk1.ifcell2
      end
   endgenerate
`ifdef verilator
   always @ (posedge clk) if (namedif2.genblk1.ifcell2.one !== 1'b1) $stop;
//`else // NOT SUPPORTED accoring to spec - generic block references
`endif

   generate
      if (1'b1)
	begin : namedif3
	   One ifcell3();  // namedif3.ifcell3
	end
   endgenerate
   always @ (posedge clk) if (namedif3.ifcell3.one !== 1'b1) $stop;

   // CASE
   generate
      case (1'b1)
	1'b1 :
	  One casecell10();	// genblk3.casecell10
      endcase
   endgenerate
`ifdef verilator
   always @ (posedge clk) if (genblk3.casecell10.one !== 1'b1) $stop;
//`else // NOT SUPPORTED accoring to spec - generic block references
`endif

   generate
      case (1'b1)
	1'b1 : begin : namedcase11
	  One casecell11();
	end
      endcase
   endgenerate
   always @ (posedge clk) if (namedcase11.casecell11.one !== 1'b1) $stop;

   genvar i;
   genvar j;

   // IF
   generate
      for (i = 0; i < 2; i = i + 1)
	One cellfor20 ();	// genblk4[0..1].cellfor20
   endgenerate
`ifdef verilator
   always @ (posedge clk) if (genblk4[0].cellfor20.one !== 1'b1) $stop;
   always @ (posedge clk) if (genblk4[1].cellfor20.one !== 1'b1) $stop;
//`else // NOT SUPPORTED accoring to spec - generic block references
`endif

   // COMBO
   generate
      for (i = 0; i < 2; i = i + 1)
	begin : namedfor21
	   One cellfor21 ();	// namedfor21[0..1].cellfor21
	end
   endgenerate
   always @ (posedge clk) if (namedfor21[0].cellfor21.one !== 1'b1) $stop;
   always @ (posedge clk) if (namedfor21[1].cellfor21.one !== 1'b1) $stop;

   generate
      for (i = 0; i < 2; i = i + 1)
	begin : namedfor30
	   for (j = 0; j < 2; j = j + 1)
	     begin : forb30
		if (j == 0)
		  begin : forif30
		     One cellfor30a ();  // namedfor30[0..1].forb30[0].forif30.cellfor30a
		  end
		else
`ifdef verilator
		  begin : forif30b
`else
		  begin : forif30 // forif30 seems to work on some simulators, not verilator yet
`endif
		     One cellfor30b ();  // namedfor30[0..1].forb30[1].forif30.cellfor30b
		  end
	     end
	end
   endgenerate
   always @ (posedge clk) if (namedfor30[0].forb30[0].forif30.cellfor30a.one !== 1'b1) $stop;
   always @ (posedge clk) if (namedfor30[1].forb30[0].forif30.cellfor30a.one !== 1'b1) $stop;
`ifdef verilator
   always @ (posedge clk) if (namedfor30[0].forb30[1].forif30b.cellfor30b.one !== 1'b1) $stop;
   always @ (posedge clk) if (namedfor30[1].forb30[1].forif30b.cellfor30b.one !== 1'b1) $stop;
`else
   always @ (posedge clk) if (namedfor30[0].forb30[1].forif30.cellfor30b.one !== 1'b1) $stop;
   always @ (posedge clk) if (namedfor30[1].forb30[1].forif30.cellfor30b.one !== 1'b1) $stop;
`endif

endmodule
