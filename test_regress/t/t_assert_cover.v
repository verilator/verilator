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
   reg 	 toggle;
   integer cyc; initial cyc=1;

   Test test (/*AUTOINST*/
	      // Inputs
	      .clk			(clk),
	      .toggle			(toggle),
	      .cyc			(cyc[31:0]));

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 toggle <= !cyc[0];
	 if (cyc==9) begin
	 end
	 if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule

module Test
  (
   input clk,
   input toggle,
   input [31:0] cyc
   );

   // Simple cover
   cover property (@(posedge clk) cyc==3);

   // With statement, in generate
   generate if (1) begin
      cover property (@(posedge clk) cyc==4) $display("*COVER: Cyc==4");
   end
   endgenerate

   // Labeled cover
   cyc_eq_5:
     cover property (@(posedge clk) cyc==5) $display("*COVER: Cyc==5");

   // Using default clock
   default clocking @(posedge clk); endclocking
   cover property (cyc==6) $display("*COVER: Cyc==6");

   // Disable statement
   // Note () after disable are required
   cover property (@(posedge clk) disable iff (toggle) cyc==8)
     $display("*COVER: Cyc==8");
   cover property (@(posedge clk) disable iff (!toggle) cyc==8)
     $stop;

   always_ff @ (posedge clk) begin
      labeled_icov: cover (cyc==3 || cyc==4);
   end

   // Immediate cover
   labeled_imm0: cover #0 (cyc == 0);
   labeled_immf: cover final (cyc == 0);

   // Immediate assert
   labeled_imas: assert #0 (1);
   assert final (1);

   //============================================================
   // Using a macro and generate
   wire reset = (cyc < 2);

`define covclk(eqn) cover property (@(posedge clk) disable iff (reset) (eqn))

   genvar i;
   generate
      for (i=0; i<32; i=i+1)
	begin: cycval
	   CycCover_i: `covclk( cyc[i] );
	end
   endgenerate

`ifndef verilator // Unsupported
   //============================================================
   // Using a more complicated property
   property C1;
      @(posedge clk)
	disable iff (!toggle)
	cyc==5;
   endproperty
   cover property (C1) $display("*COVER: Cyc==5");

   // Using covergroup
   // Note a covergroup is really inheritance of a special system "covergroup" class.
   covergroup counter1 @ (posedge cyc);
      // Automatic methods:  stop(), start(), sample(), set_inst_name()

      // Each bin value must be <= 32 bits.  Strange.
      cyc_value : coverpoint cyc {
	}

      cyc_bined : coverpoint cyc {
	 bins zero    = {0};
	 bins low    = {1,5};
	 // Note 5 is also in the bin above.  Only the first bin matching is counted.
	 bins mid   = {[5:$]};
	 // illegal_bins	// Has precidence over "first matching bin", creates assertion
	 // ignore_bins		// Not counted, and not part of total
      }
      toggle : coverpoint (toggle) {
	 bins off  = {0};
	 bins on   = {1};
      }
      cyc5 : coverpoint (cyc==5) {
	 bins five  = {1};
      }

      // option.at_least = {number};	// Default 1 - Hits to be considered covered
      // option.auto_bin_max = {number}; // Default 64
      // option.comment = {string}
      // option.goal = {number};	// Default 90%
      // option.name = {string}
      // option.per_instance = 1;	// Default 0 - each instance separately counted (cadence default is 1)
      // option.weight = {number};	// Default 1

      // CROSS
      value_and_toggle:  // else default is __<firstlabel>_X_<secondlabel>_<n>
	cross cyc_value, toggle;
   endgroup
   counter1 c1 = new();
`endif

endmodule
