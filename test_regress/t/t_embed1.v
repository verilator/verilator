// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire   bit_in = crc[0];
   wire [30:0]  vec_in = crc[31:1];
   wire [123:0] wide_in = {crc[59:0],~crc[63:0]};

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire			exp_bit_out;		// From reference of t_embed1_child.v
   wire			exp_did_init_out;	// From reference of t_embed1_child.v
   wire [30:0]		exp_vec_out;		// From reference of t_embed1_child.v
   wire [123:0]		exp_wide_out;		// From reference of t_embed1_child.v
   wire			got_bit_out;		// From test of t_embed1_wrap.v
   wire			got_did_init_out;	// From test of t_embed1_wrap.v
   wire [30:0]		got_vec_out;		// From test of t_embed1_wrap.v
   wire [123:0]		got_wide_out;		// From test of t_embed1_wrap.v
   // End of automatics

   // A non-embedded master

   /* t_embed1_child AUTO_TEMPLATE(
      .\(.*_out\)  (exp_\1[]),
      .is_ref (1'b1));
    */
   t_embed1_child reference
     (/*AUTOINST*/
      // Outputs
      .bit_out				(exp_bit_out),		 // Templated
      .vec_out				(exp_vec_out[30:0]),	 // Templated
      .wide_out				(exp_wide_out[123:0]),	 // Templated
      .did_init_out			(exp_did_init_out),	 // Templated
      // Inputs
      .clk				(clk),
      .bit_in				(bit_in),
      .vec_in				(vec_in[30:0]),
      .wide_in				(wide_in[123:0]),
      .is_ref				(1'b1));			 // Templated

   // The embeded comparison

   /* t_embed1_wrap AUTO_TEMPLATE(
      .\(.*_out\)  (got_\1[]),
      .is_ref (1'b0));
    */

   t_embed1_wrap test
     (/*AUTOINST*/
      // Outputs
      .bit_out				(got_bit_out),		 // Templated
      .vec_out				(got_vec_out[30:0]),	 // Templated
      .wide_out				(got_wide_out[123:0]),	 // Templated
      .did_init_out			(got_did_init_out),	 // Templated
      // Inputs
      .clk				(clk),
      .bit_in				(bit_in),
      .vec_in				(vec_in[30:0]),
      .wide_in				(wide_in[123:0]),
      .is_ref				(1'b0));			 // Templated

   // Aggregate outputs into a single result vector
   wire [63:0] result = {60'h0,
			 got_wide_out !== exp_wide_out,
			 got_vec_out !== exp_vec_out,
			 got_bit_out !== exp_bit_out,
			 got_did_init_out !== exp_did_init_out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x gv=%x ev=%x\n",$time, cyc, crc, result,
	     got_vec_out, exp_vec_out);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
      end
      else if (cyc<90) begin
	 if (result != 64'h0) begin
	    $display("Bit mismatch, result=%x\n", result);
	    $stop;
	 end
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 //Child prints this: $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
