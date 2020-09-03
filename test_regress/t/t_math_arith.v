// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   reg 	 _ranit;

   reg [2:0] xor3;
   reg [1:0] xor2;
   reg [0:0] xor1;
   reg [2:0] ma, mb;
   reg [9:0] mc;
   reg [4:0] mr1;
   reg [30:0] mr2;

   reg [67:0] sh1;
   reg [67:0] shq;

   wire       foo, bar;   assign {foo,bar} = 2'b1_0;

   // surefire lint_off STMINI
   initial _ranit = 0;

   wire [4:0] cond_check = ((  xor2 == 2'b11) ? 5'h1
                            : (xor2 == 2'b00) ? 5'h2
			    : (xor2 == 2'b01) ? 5'h3
			    : 5'h4);

   wire       ctrue  = 1'b1 ? cond_check[1] : cond_check[0];
   wire       cfalse = 1'b0 ? cond_check[1] : cond_check[0];
   wire       cif    = cond_check[2] ? cond_check[1] : cond_check[0];
   wire       cifn   = (!cond_check[2]) ? cond_check[1] : cond_check[0];

   wire [4:0] doubleconc = {1'b0, 1'b1, 1'b0, cond_check[0], 1'b1};

   wire       zero = 1'b0;
   wire       one = 1'b1;
   wire [5:0] rep6 = {6{one}};

   // verilator lint_off WIDTH
   localparam [3:0] bug764_p11 = 1'bx;
   // verilator lint_on WIDTH

   always @ (posedge clk) begin
      if (!_ranit) begin
	 _ranit <= 1;

	 if (rep6 != 6'b111111) $stop;
	 if (!one) $stop;
	 if (~one) $stop;

	 if (( 1'b0 ? 3'h3 : 1'b0 ? 3'h2 : 1'b1 ? 3'h1 : 3'h0) !== 3'h1) $stop;
	 // verilator lint_off WIDTH
	 if (( 8'h10 + 1'b0 ? 8'he : 8'hf) !== 8'he) $stop;  // + is higher than ?
	 // verilator lint_on WIDTH

	 // surefire lint_off SEQASS
	 xor1 = 1'b1;
	 xor2 = 2'b11;
	 xor3 = 3'b111;
	 // verilator lint_off WIDTH
	 if (1'b1 & | (!xor3)) $stop;
	 // verilator lint_on WIDTH
	 if ({1{xor1}} != 1'b1) $stop;
	 if ({4{xor1}} != 4'b1111) $stop;
	 if (!(~xor1)  !== ~(!xor1)) $stop;
	 if ((^xor1)  !== 1'b1) $stop;
	 if ((^xor2)  !== 1'b0) $stop;
	 if ((^xor3)  !== 1'b1) $stop;
	 if (~(^xor2) !== 1'b1) $stop;
	 if (~(^xor3) !== 1'b0) $stop;
	 if ((^~xor1) !== 1'b0) $stop;
	 if ((^~xor2) !== 1'b1) $stop;
	 if ((^~xor3) !== 1'b0) $stop;
	 if ((~^xor1) !== 1'b0) $stop;
	 if ((~^xor2) !== 1'b1) $stop;
	 if ((~^xor3) !== 1'b0) $stop;
	 xor1 = 1'b0;
	 xor2 = 2'b10;
	 xor3 = 3'b101;
	 if ((^xor1)  !== 1'b0) $stop;
	 if ((^xor2)  !== 1'b1) $stop;
	 if ((^xor3)  !== 1'b0) $stop;
	 if (~(^xor2) !== 1'b0) $stop;
	 if (~(^xor3) !== 1'b1) $stop;
	 if ((^~xor1) !== 1'b1) $stop;
	 if ((^~xor2) !== 1'b0) $stop;
	 if ((^~xor3) !== 1'b1) $stop;
	 if ((~^xor1) !== 1'b1) $stop;
	 if ((~^xor2) !== 1'b0) $stop;
	 if ((~^xor3) !== 1'b1) $stop;

	 ma = 3'h3;
         mb = 3'h4;
	 mc = 10'h5;

         mr1 = ma * mb; 	 // Lint ASWESB: Assignment width mismatch
	 mr2 = 30'h5 * mc; 	 // Lint ASWESB: Assignment width mismatch
	 if (mr1 !== 5'd12) $stop;
	 if (mr2 !== 31'd25) $stop; // Lint CWECBB: Comparison width mismatch

	 sh1 = 68'hf_def1_9abc_5678_1234;
	 shq = sh1 >> 16;
	 if (shq !== 68'hf_def1_9abc_5678) $stop;
	 shq = sh1 << 16; 	 // Lint ASWESB: Assignment width mismatch
	 if (shq !== 68'h1_9abc_5678_1234_0000) $stop;

	 // surefire lint_on SEQASS

	 // Test display extraction widthing
	 $display("[%0t] %x %x %x(%d)", $time, shq[2:0], shq[2:0]<<2, xor3[2:0], xor3[2:0]);

	 // bug736
	 //verilator lint_off WIDTH
	 if ((~| 4'b0000) != 4'b0001) $stop;
	 if ((~| 4'b0010) != 4'b0000) $stop;
	 if ((~& 4'b1111) != 4'b0000) $stop;
	 if ((~& 4'b1101) != 4'b0001) $stop;
	 //verilator lint_on WIDTH

	 // bug764
	 //verilator lint_off WIDTH
	 // X does not sign extend
	 if (bug764_p11 !== 4'b000x) $stop;
	 if (~& bug764_p11 !== 1'b1) $stop;
	 //verilator lint_on WIDTH
	 // However IEEE 2017 5.7.1 says for constants that smaller-sizes do extend
	 if (4'bx !== 4'bxxxx) $stop;
	 if (4'bz !== 4'bzzzz) $stop;
	 if (4'b1 !== 4'b0001) $stop;

         if ((0 -> 0) != 1'b1) $stop;
         if ((0 -> 1) != 1'b1) $stop;
         if ((1 -> 0) != 1'b0) $stop;
         if ((1 -> 1) != 1'b1) $stop;

         if ((0 <-> 0) != 1'b1) $stop;
         if ((0 <-> 1) != 1'b0) $stop;
         if ((1 <-> 0) != 1'b0) $stop;
         if ((1 <-> 1) != 1'b1) $stop;

         $write("*-* All Finished *-*\n");
         $finish;
      end
   end


   reg [63:0]  m_data_pipe2_r;
   reg [31:0]  m_corr_data_w0, m_corr_data_w1;
   reg [7:0]   m_corr_data_b8;
   initial begin
      m_data_pipe2_r = 64'h1234_5678_9abc_def0;
      {m_corr_data_b8, m_corr_data_w1, m_corr_data_w0} = { m_data_pipe2_r[63:57], 1'b0,	//m_corr_data_b8 [7:0]
							   m_data_pipe2_r[56:26], 1'b0,	//m_corr_data_w1 [31:0]
							   m_data_pipe2_r[25:11], 1'b0,	//m_corr_data_w0 [31:16]
							   m_data_pipe2_r[10:04], 1'b0,	//m_corr_data_w0 [15:8]
							   m_data_pipe2_r[03:01], 1'b0,	//m_corr_data_w0 [7:4]
							   m_data_pipe2_r[0],     3'b000	//m_corr_data_w0 [3:0]
							   };
      if (m_corr_data_w0 != 32'haf36de00) $stop;
      if (m_corr_data_w1 != 32'h1a2b3c4c) $stop;
      if (m_corr_data_b8 != 8'h12) $stop;
   end

endmodule
