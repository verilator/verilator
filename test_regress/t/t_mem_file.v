// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=0;
   reg [63:0] crc;
   reg [63:0] sum;

   wire		r1_en /*verilator public*/ = crc[12];
   wire [1:0] 	r1_ad /*verilator public*/ = crc[9:8];
   wire 	r2_en /*verilator public*/ = 1'b1;
   wire [1:0] 	r2_ad /*verilator public*/ = crc[11:10];
   wire 	w1_en /*verilator public*/ = crc[5];
   wire [1:0] 	w1_a  /*verilator public*/ = crc[1:0];
   wire [63:0] 	w1_d  /*verilator public*/ = {2{crc[63:32]}};
   wire 	w2_en /*verilator public*/ = crc[4];
   wire [1:0] 	w2_a  /*verilator public*/ = crc[3:2];
   wire [63:0] 	w2_d  /*verilator public*/ = {2{~crc[63:32]}};

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [63:0]		r1_d_d2r;		// From file of file.v
   wire [63:0]		r2_d_d2r;		// From file of file.v
   // End of automatics

   file file (/*AUTOINST*/
	      // Outputs
	      .r1_d_d2r			(r1_d_d2r[63:0]),
	      .r2_d_d2r			(r2_d_d2r[63:0]),
	      // Inputs
	      .clk			(clk),
	      .r1_en			(r1_en),
	      .r1_ad			(r1_ad[1:0]),
	      .r2_en			(r2_en),
	      .r2_ad			(r2_ad[1:0]),
	      .w1_en			(w1_en),
	      .w1_a			(w1_a[1:0]),
	      .w1_d			(w1_d[63:0]),
	      .w2_en			(w2_en),
	      .w2_a			(w2_a[1:0]),
	      .w2_d			(w2_d[63:0]));

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d EN=%b%b%b%b R0=%x R1=%x\n",$time, cyc, r1_en,r2_en,w1_en,w2_en, r1_d_d2r, r2_d_d2r);
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= {r1_d_d2r ^ r2_d_d2r} ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
	 // We've manually verified all X's are out of the design by this point
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $write("[%0t] cyc==%0d crc=%x %x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 if (sum !== 64'h5e9ea8c33a97f81e) $stop;
	 $finish;
      end
   end

endmodule

module file (/*AUTOARG*/
   // Outputs
   r1_d_d2r, r2_d_d2r,
   // Inputs
   clk, r1_en, r1_ad, r2_en, r2_ad, w1_en, w1_a, w1_d, w2_en, w2_a, w2_d
   );

   input	   clk;
   input 	   r1_en;
   input [1:0] 	   r1_ad;
   output [63:0]   r1_d_d2r;
   input 	   r2_en;
   input [1:0] 	   r2_ad;
   output [63:0]   r2_d_d2r;
   input 	   w1_en;
   input [1:0] 	   w1_a;
   input [63:0]    w1_d;
   input 	   w2_en;
   input [1:0] 	   w2_a;
   input [63:0]    w2_d;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   // End of automatics
   /*AUTOREG*/
   // Beginning of automatic regs (for this module's undeclared outputs)
   reg [63:0]		r1_d_d2r;
   reg [63:0]		r2_d_d2r;
   // End of automatics

   // Writes
   wire [3:0] 	   m_w1_onehotwe = ({4{w1_en}} & (4'b1 << w1_a));
   wire [3:0] 	   m_w2_onehotwe = ({4{w2_en}} & (4'b1 << w2_a));

   wire [63:0] 	   rg0_wrdat = m_w1_onehotwe[0] ? w1_d : w2_d;
   wire [63:0] 	   rg1_wrdat = m_w1_onehotwe[1] ? w1_d : w2_d;
   wire [63:0] 	   rg2_wrdat = m_w1_onehotwe[2] ? w1_d : w2_d;
   wire [63:0] 	   rg3_wrdat = m_w1_onehotwe[3] ? w1_d : w2_d;

   wire [3:0] 	   m_w_onehotwe = m_w1_onehotwe | m_w2_onehotwe;

   // Storage
   reg [63:0] 	   m_rg0_r;
   reg [63:0] 	   m_rg1_r;
   reg [63:0] 	   m_rg2_r;
   reg [63:0] 	   m_rg3_r;

   always @ (posedge clk) begin
      if (m_w_onehotwe[0]) m_rg0_r <= rg0_wrdat;
      if (m_w_onehotwe[1]) m_rg1_r <= rg1_wrdat;
      if (m_w_onehotwe[2]) m_rg2_r <= rg2_wrdat;
      if (m_w_onehotwe[3]) m_rg3_r <= rg3_wrdat;
   end

   // Reads
   reg [1:0] 		m_r1_ad_d1r;
   reg [1:0] 		m_r2_ad_d1r;
   reg [1:0] 		m_ren_d1r;

   always @ (posedge clk) begin
      if (r1_en) m_r1_ad_d1r <= r1_ad;
      if (r2_en) m_r2_ad_d1r <= r2_ad;
      m_ren_d1r <= {r2_en, r1_en};
   end

   // Scheme1: shift...
   wire [3:0] 	   m_r1_onehot_d1 = (4'b1 << m_r1_ad_d1r);
   // Scheme2: bit mask
   reg [3:0] 	   m_r2_onehot_d1;
   always @* begin
      m_r2_onehot_d1 = 4'd0;
      m_r2_onehot_d1[m_r2_ad_d1r] = 1'b1;
   end

   wire [63:0] 	   m_r1_d_d1 = (({64{m_r1_onehot_d1[0]}} & m_rg0_r) |
				({64{m_r1_onehot_d1[1]}} & m_rg1_r) |
				({64{m_r1_onehot_d1[2]}} & m_rg2_r) |
				({64{m_r1_onehot_d1[3]}} & m_rg3_r));

   wire [63:0] 	   m_r2_d_d1 = (({64{m_r2_onehot_d1[0]}} & m_rg0_r) |
				({64{m_r2_onehot_d1[1]}} & m_rg1_r) |
				({64{m_r2_onehot_d1[2]}} & m_rg2_r) |
				({64{m_r2_onehot_d1[3]}} & m_rg3_r));

   always @ (posedge clk) begin
      if (m_ren_d1r[0]) r1_d_d2r <= m_r1_d_d1;
      if (m_ren_d1r[1]) r2_d_d2r <= m_r2_d_d1;
   end

endmodule
