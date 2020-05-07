// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   integer 	cyc=0;

   genvar 	g;
   integer 	i;

   reg [31:0] v;

   reg [31:0] gen_pre_PLUSPLUS = 32'h0;
   reg [31:0] gen_pre_MINUSMINUS = 32'h0;
   reg [31:0] gen_post_PLUSPLUS	= 32'h0;
   reg [31:0] gen_post_MINUSMINUS = 32'h0;
   reg [31:0] gen_PLUSEQ = 32'h0;
   reg [31:0] gen_MINUSEQ = 32'h0;
   reg [31:0] gen_TIMESEQ = 32'h0;
   reg [31:0] gen_DIVEQ = 32'h0;
   reg [31:0] gen_MODEQ = 32'h0;
   reg [31:0] gen_ANDEQ = 32'h0;
   reg [31:0] gen_OREQ = 32'h0;
   reg [31:0] gen_XOREQ	= 32'h0;
   reg [31:0] gen_SLEFTEQ = 32'h0;
   reg [31:0] gen_SRIGHTEQ = 32'h0;
   reg [31:0] gen_SSRIGHTEQ = 32'h0;

   generate
      for (g=8; g<=16; ++g) always @(posedge clk) gen_pre_PLUSPLUS[g] = 1'b1;
      for (g=16; g>=8; --g) always @(posedge clk) gen_pre_MINUSMINUS[g] = 1'b1;
      for (g=8; g<=16; g++) always @(posedge clk) gen_post_PLUSPLUS[g] = 1'b1;
      for (g=16; g>=8; g--) always @(posedge clk) gen_post_MINUSMINUS[g] = 1'b1;
      for (g=8; g<=16; g+=2) always @(posedge clk) gen_PLUSEQ[g] = 1'b1;
      for (g=16; g>=8; g-=2) always @(posedge clk) gen_MINUSEQ[g] = 1'b1;
`ifndef verilator //UNSUPPORTED
      for (g=8; g<=16; g*=2) always @(posedge clk) gen_TIMESEQ[g] = 1'b1;
      for (g=16; g>=8; g/=2) always @(posedge clk) gen_DIVEQ[g] = 1'b1;
      for (g=15; g>8;  g%=8) always @(posedge clk) gen_MODEQ[g] = 1'b1;
      for (g=7; g>4;   g&=4) always @(posedge clk) gen_ANDEQ[g] = 1'b1;
      for (g=1; g<=1;  g|=2) always @(posedge clk) gen_OREQ[g] = 1'b1;
      for (g=7; g==7;  g^=2) always @(posedge clk) gen_XOREQ[g] = 1'b1;
      for (g=8; g<=16; g<<=2) always @(posedge clk) gen_SLEFTEQ[g] = 1'b1;
      for (g=16; g>=8; g>>=2) always @(posedge clk) gen_SRIGHTEQ[g] = 1'b1;
      for (g=16; g>=8; g>>>=2) always @(posedge clk) gen_SSRIGHTEQ[g] = 1'b1;
`endif
   endgenerate

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 3) begin
`ifdef TEST_VERBOSE
	 $write("gen_pre_PLUSPLUS     %b\n", gen_pre_PLUSPLUS);
	 $write("gen_pre_MINUSMINUS   %b\n", gen_pre_MINUSMINUS);
	 $write("gen_post_PLUSPLUS    %b\n", gen_post_PLUSPLUS);
	 $write("gen_post_MINUSMINUS  %b\n", gen_post_MINUSMINUS);
	 $write("gen_PLUSEQ           %b\n", gen_PLUSEQ);
	 $write("gen_MINUSEQ          %b\n", gen_MINUSEQ);
	 $write("gen_TIMESEQ          %b\n", gen_TIMESEQ);
	 $write("gen_DIVEQ            %b\n", gen_DIVEQ);
	 $write("gen_MODEQ            %b\n", gen_MODEQ);
	 $write("gen_ANDEQ            %b\n", gen_ANDEQ);
	 $write("gen_OREQ             %b\n", gen_OREQ);
	 $write("gen_XOREQ            %b\n", gen_XOREQ);
	 $write("gen_SLEFTEQ          %b\n", gen_SLEFTEQ);
	 $write("gen_SRIGHTEQ         %b\n", gen_SRIGHTEQ);
	 $write("gen_SSRIGHTEQ        %b\n", gen_SSRIGHTEQ);
`endif
	 if (gen_pre_PLUSPLUS	!== 32'b00000000000000011111111100000000) $stop;
	 if (gen_pre_MINUSMINUS	!== 32'b00000000000000011111111100000000) $stop;
	 if (gen_post_PLUSPLUS	!== 32'b00000000000000011111111100000000) $stop;
	 if (gen_post_MINUSMINUS!== 32'b00000000000000011111111100000000) $stop;
	 if (gen_PLUSEQ		!== 32'b00000000000000010101010100000000) $stop;
	 if (gen_MINUSEQ	!== 32'b00000000000000010101010100000000) $stop;
`ifndef verilator //UNSUPPORTED
	 if (gen_TIMESEQ	!== 32'b00000000000000010000000100000000) $stop;
	 if (gen_DIVEQ		!== 32'b00000000000000010000000100000000) $stop;
	 if (gen_MODEQ		!== 32'b00000000000000001000000000000000) $stop;
	 if (gen_ANDEQ		!== 32'b00000000000000000000000010000000) $stop;
	 if (gen_OREQ		!== 32'b00000000000000000000000000000010) $stop;
	 if (gen_XOREQ		!== 32'b00000000000000000000000010000000) $stop;
	 if (gen_SLEFTEQ	!== 32'b00000000000000000000000100000000) $stop;
	 if (gen_SRIGHTEQ	!== 32'b00000000000000010000000000000000) $stop;
	 if (gen_SSRIGHTEQ	!== 32'b00000000000000010000000000000000) $stop;
`endif

	 v=0; for (i=8; i<=16; ++i)  v[i] = 1'b1; if (v !== 32'b00000000000000011111111100000000) $stop;
	 v=0; for (i=16; i>=8; --i)  v[i] = 1'b1; if (v !== 32'b00000000000000011111111100000000) $stop;
	 v=0; for (i=8; i<=16; i++)  v[i] = 1'b1; if (v !== 32'b00000000000000011111111100000000) $stop;
	 v=0; for (i=16; i>=8; i--)  v[i] = 1'b1; if (v !== 32'b00000000000000011111111100000000) $stop;
	 v=0; for (i=8; i<=16; i+=2) v[i] = 1'b1; if (v !== 32'b00000000000000010101010100000000) $stop;
	 v=0; for (i=16; i>=8; i-=2) v[i] = 1'b1; if (v !== 32'b00000000000000010101010100000000) $stop;
`ifndef verilator //UNSUPPORTED
	 v=0; for (i=8; i<=16; i*=2) v[i] = 1'b1; if (v !== 32'b00000000000000010000000100000000) $stop;
	 v=0; for (i=16; i>=8; i/=2) v[i] = 1'b1; if (v !== 32'b00000000000000010000000100000000) $stop;
	 v=0; for (i=15; i>8;  i%=8) v[i] = 1'b1; if (v !== 32'b00000000000000001000000000000000) $stop;
	 v=0; for (i=7; i>4;   i&=4) v[i] = 1'b1; if (v !== 32'b00000000000000000000000010000000) $stop;
	 v=0; for (i=1; i<=1;  i|=2) v[i] = 1'b1; if (v !== 32'b00000000000000000000000000000010) $stop;
	 v=0; for (i=7; i==7;  i^=2) v[i] = 1'b1; if (v !== 32'b00000000000000000000000010000000) $stop;
	 v=0; for (i=8; i<=16; i<<=2) v[i] =1'b1; if (v !== 32'b00000000000000000000000100000000) $stop;
	 v=0; for (i=16; i>=8; i>>=2) v[i] =1'b1; if (v !== 32'b00000000000000010000000000000000) $stop;
	 v=0; for (i=16; i>=8; i>>>=2) v[i]=1'b1; if (v !== 32'b00000000000000010000000000000000) $stop;
`endif
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
