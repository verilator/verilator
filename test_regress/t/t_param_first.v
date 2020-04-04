// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg 	 _ranit;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [4:0]		par1;			// From a1 of t_param_first_a.v
   wire [4:0]		par2;			// From a2 of t_param_first_a.v
   wire [4:0]		par3;			// From a3 of t_param_first_a.v
   wire [4:0]		par4;			// From a4 of t_param_first_a.v
   wire [1:0]		varwidth1;		// From a1 of t_param_first_a.v
   wire [2:0]		varwidth2;		// From a2 of t_param_first_a.v
   wire [3:0]		varwidth3;		// From a3 of t_param_first_a.v
   wire [3:0]		varwidth4;		// From a4 of t_param_first_a.v
   // End of automatics
   /*t_param_first_a AUTO_TEMPLATE (
		      .par		(par@[]));
		      .varwidth		(varwidth@[]));
    */

   parameter XX = 2'bXX;

   parameter THREE = 3;

   t_param_first_a #(1,5) a1
     (
      // Outputs
      .varwidth		(varwidth1[1:0]),
      /*AUTOINST*/
      // Outputs
      .par				(par1[4:0]));		 // Templated
   t_param_first_a #(2,5) a2
     (
      // Outputs
      .varwidth		(varwidth2[2:0]),
      /*AUTOINST*/
      // Outputs
      .par				(par2[4:0]));		 // Templated
   t_param_first_a #(THREE,5) a3
     (
      // Outputs
      .varwidth		(varwidth3[3:0]),
      /*AUTOINST*/
      // Outputs
      .par				(par3[4:0]));		 // Templated
   t_param_first_a #(THREE,5) a4
     (
      // Outputs
      .varwidth		(varwidth4[3:0]),
      /*AUTOINST*/
      // Outputs
      .par				(par4[4:0]));		 // Templated

   parameter THREE_BITS_WIDE = 3'b011;
   parameter THREE_2WIDE = 2'b11;
   parameter ALSO_THREE_WIDE = THREE_BITS_WIDE;
   parameter THREEPP_32_WIDE = 2*8*2+3;
   parameter THREEPP_3_WIDE = 3'd4*3'd4*3'd2+3'd3;  // Yes folks VCS says 3 bits wide

   // Width propagation doesn't care about LHS vs RHS
   // But the width of a RHS/LHS on a upper node does affect lower nodes;
   // Thus must double-descend in width analysis.
   // VCS 7.0.1 is broken on this test!
   parameter T10 = (3'h7+3'h7)+4'h0;	//initial if (T10!==4'd14) $stop;
   parameter T11 = 4'h0+(3'h7+3'h7);	//initial if (T11!==4'd14) $stop;

   // Parameters assign LHS is affectively width zero.
   parameter T12 = THREE_2WIDE + THREE_2WIDE;	initial if (T12!==2'd2) $stop;
   parameter T13 = THREE_2WIDE + 3;		initial if (T13!==32'd6) $stop;

   // Must be careful about LSB's with extracts
   parameter [39:8] T14 = 32'h00_1234_56;  initial if (T14[24:16]!==9'h34) $stop;

   //
   parameter THREEPP_32P_WIDE = 3'd4*3'd4*2+3'd3;
   parameter THREE_32_WIDE = 3%32;
   parameter THIRTYTWO = 2;	// Param is 32 bits
   parameter [40:0] WIDEPARAM = 41'h12_3456789a;
   parameter [40:0] WIDEPARAM2 = WIDEPARAM;

   reg [7:0] eightb;
   reg [3:0] fourb;
   wire [7:0] eight = 8'b00010000;
   wire [1:0] eight2two = eight[THREE_32_WIDE+1:THREE_32_WIDE];
   wire [2:0] threebits = ALSO_THREE_WIDE;

   // surefire lint_off CWCCXX

   initial _ranit = 0;

   always @ (posedge clk) begin
      if (!_ranit) begin
	 _ranit <= 1;
	 $write("[%0t] t_param: Running\n", $time);
	 //
	 $write("  %d %d %d\n", par1,par2,par3);
	 if (par1!==5'd1) $stop;
	 if (par2!==5'd2) $stop;
	 if (par3!==5'd3) $stop;
	 if (par4!==5'd3) $stop;
	 if (varwidth1!==2'd2) $stop;
	 if (varwidth2!==3'd2) $stop;
	 if (varwidth3!==4'd2) $stop;
	 if (varwidth4!==4'd2) $stop;
	 if (threebits !== 3'b011) $stop;
	 if (eight !== 8'b00010000) $stop;
	 if (eight2two !== 2'b10) $stop;
	 $write(" Params = %b %b\n   %b %b\n",
		THREEPP_32_WIDE,THREEPP_3_WIDE,
		THIRTYTWO, THREEPP_32P_WIDE);
	 if (THREEPP_32_WIDE !== 32'h23) $stop;
	 if (THREEPP_3_WIDE !== 3'h3) $stop;
	 if (THREEPP_32P_WIDE !== 32'h23) $stop;
	 if (THIRTYTWO[1:0] !== 2'h2) $stop;
	 if (THIRTYTWO !== 32'h2) $stop;
	 if (THIRTYTWO !== 2) $stop;
	 if ((THIRTYTWO[1:0]+2'b00) !== 2'b10) $stop;
	 if ({1'b1,{THIRTYTWO[1:0]+2'b00}} !== 3'b110) $stop;
	 if (XX===0 || XX===1 || XX===2 || XX===3) $stop;  // Paradoxical but right, since 1'bx!=0 && !=1
	 //
	 // Example of assignment LHS affecting expression widths.
	 // verilator lint_off WIDTH
	 // surefire lint_off ASWCMB
	 // surefire lint_off ASWCBB
	 eightb = (4'd8+4'd8)/4'd4;	if (eightb!==8'd4) $stop;
	 fourb = (4'd8+4'd8)/4'd4;	if (fourb!==4'd0) $stop;
	 fourb = (4'd8+8)/4'd4;		if (fourb!==4'd4) $stop;
	 // verilator lint_on WIDTH
	 // surefire lint_on ASWCMB
	 // surefire lint_on ASWCBB
	 //
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
