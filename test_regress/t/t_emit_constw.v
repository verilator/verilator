// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2015 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkhw(gotv,w,expv) do if (gotv[(w)*32+:$bits(expv)] !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv[(w)*32+:32]), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   bit [4*32-1:0] w4 = {32'h7c709753, 32'hbc8f6059, 32'h3b0db464, 32'h721a8fad};

   bit [8*32-2:0] w8m = {31'h7146e1bf, 32'ha8549e42, 32'hca6960bd, 32'h191b7f9b, 32'h93d79866, 32'hf4489e2b, 32'h8e9a3236, 32'h1d2a2d1d};

   bit [8*32-1:0] w8 = {32'hc211addc, 32'he5d4a057, 32'h5cbf88fe, 32'h42cf42e2, 32'heb584263, 32'ha585f118, 32'h231531c8, 32'hc73f7b06};

   bit [8*32-0:0] w8p = {1'b1, 32'h096aa54b, 32'h48aae18e, 32'hf9502cea, 32'h518c8b61, 32'h9e8641a2, 32'h0dc0249c, 32'hd421a87a, 32'hb8ee9199};

   bit [9*32-1:0] w9 = {32'hca800ac1,
			32'h0de4823a, 32'ha51663ac, 32'h96351446, 32'h6b0bbcd5, 32'h4a64b530, 32'h4967d59a, 32'hfcc17292, 32'h57926621};

   bit [16*32-2:0] w16m = {31'h77ad72c7, 32'h73aa9cbb, 32'h7ecf026d, 32'h985a3ed2, 32'hfe961c1d, 32'h7a01df72, 32'h79e13d71, 32'hb69e2e32,
			   32'h09fcbc45, 32'hcfd738c1, 32'hc197ac7c, 32'hc316d727, 32'h903034e4, 32'h92a047d1, 32'h6a5357af, 32'ha82ce9c8};

   bit [16*32-1:0] w16 = {32'he49548a7, 32'ha02336a2, 32'h2bb48f0d, 32'h9974e098, 32'h34ae644f, 32'hca46dc2c, 32'h9f71a468, 32'h64ae043e,
			  32'h7bc94d66, 32'h57aba588, 32'h5b9bb4fe, 32'hb87ed644, 32'hd34b5b20, 32'h712928de, 32'h4bdbd28e, 32'ha0576784};

   bit [16*32-0:0] w16p = {1'b1, 32'hd278a306, 32'h374ce262, 32'hb608c88e, 32'h43d3e446, 32'h42e26866, 32'h44c31148, 32'hd3db659f, 32'hb3b84b2e,
			   32'h1aa7a184, 32'h73b28538, 32'h6384e801, 32'h98d58e00, 32'h9c1d1429, 32'hb407730e, 32'he974c1fd, 32'he787c302};

   bit [17*32-1:0] w17 = {32'hf1e322ac,
			  32'hbbdbd761, 32'h760fe07d, 32'h3808cb28, 32'haf313051, 32'h37dc63b9, 32'hdddb418b, 32'he65a9d64, 32'hc1b6ab23,
			  32'h11131ac1, 32'h0050e0bc, 32'h442e3754, 32'h0eb4556e, 32'hd153064b, 32'h41349f97, 32'hb6f4149f, 32'h34bb1fb1};

   function [7:0] bytehash (input [32*32-1:0] data);
      integer i;
      bytehash = 0;
      for (i=0; i<32*32; ++i) begin
	 bytehash = {bytehash[0], bytehash[7:1]} ^ data[i +: 8];
      end
      return bytehash;
   endfunction

   // Aggregate outputs into a single result vector
   // verilator lint_off WIDTH
   wire [63:0] result = (bytehash(w4)
			 ^ bytehash(w8m)
			 ^ bytehash(w8)
			 ^ bytehash(w8p)
			 ^ bytehash(w9)
			 ^ bytehash(w16m)
			 ^ bytehash(w16)
			 ^ bytehash(w16p)
			 ^ bytehash(w17));
   // verilator lint_on WIDTH

`define EXPECTED_SUM 64'hb6fdb64085fc17f5

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
         // verilator lint_off SELRANGE
         `checkhw(w4,3,32'h7c709753);
         `checkhw(w4,2,32'hbc8f6059);
         `checkhw(w4,1,32'h3b0db464);
         `checkhw(w4,0,32'h721a8fad);
         `checkhw(w8m,7,31'h7146e1bf);
         `checkhw(w8m,6,32'ha8549e42);
         `checkhw(w8m,5,32'hca6960bd);
         `checkhw(w8m,4,32'h191b7f9b);
         `checkhw(w8m,3,32'h93d79866);
         `checkhw(w8m,2,32'hf4489e2b);
         `checkhw(w8m,1,32'h8e9a3236);
         `checkhw(w8m,0,32'h1d2a2d1d);
         `checkhw(w8,7,32'hc211addc);
         `checkhw(w8,6,32'he5d4a057);
         `checkhw(w8,5,32'h5cbf88fe);
         `checkhw(w8,4,32'h42cf42e2);
         `checkhw(w8,3,32'heb584263);
         `checkhw(w8,2,32'ha585f118);
         `checkhw(w8,1,32'h231531c8);
         `checkhw(w8,0,32'hc73f7b06);
         `checkhw(w8p,8,1'b1);
         `checkhw(w8p,7,32'h096aa54b);
         `checkhw(w8p,6,32'h48aae18e);
         `checkhw(w8p,5,32'hf9502cea);
         `checkhw(w8p,4,32'h518c8b61);
         `checkhw(w8p,3,32'h9e8641a2);
         `checkhw(w8p,2,32'h0dc0249c);
         `checkhw(w8p,1,32'hd421a87a);
         `checkhw(w8p,0,32'hb8ee9199);
         `checkhw(w9,8,32'hca800ac1);
         `checkhw(w9,7,32'h0de4823a);
         `checkhw(w9,6,32'ha51663ac);
         `checkhw(w9,5,32'h96351446);
         `checkhw(w9,4,32'h6b0bbcd5);
         `checkhw(w9,3,32'h4a64b530);
         `checkhw(w9,2,32'h4967d59a);
         `checkhw(w9,1,32'hfcc17292);
         `checkhw(w9,0,32'h57926621);
         `checkhw(w16m,15,31'h77ad72c7);
         `checkhw(w16m,14,32'h73aa9cbb);
         `checkhw(w16m,13,32'h7ecf026d);
         `checkhw(w16m,12,32'h985a3ed2);
         `checkhw(w16m,11,32'hfe961c1d);
         `checkhw(w16m,10,32'h7a01df72);
         `checkhw(w16m,9,32'h79e13d71);
         `checkhw(w16m,8,32'hb69e2e32);
         `checkhw(w16m,7,32'h09fcbc45);
         `checkhw(w16m,6,32'hcfd738c1);
         `checkhw(w16m,5,32'hc197ac7c);
         `checkhw(w16m,4,32'hc316d727);
         `checkhw(w16m,3,32'h903034e4);
         `checkhw(w16m,2,32'h92a047d1);
         `checkhw(w16m,1,32'h6a5357af);
         `checkhw(w16m,0,32'ha82ce9c8);
         // verilator lint_on SELRANGE
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
	 w4   = w4   >>> 1;
	 w8m  =	w8m  >>> 1;
	 w8   =	w8   >>> 1;
	 w8p  =	w8p  >>> 1;
	 w9   =	w9   >>> 1;
	 w16m =	w16m >>> 1;
	 w16  =	w16  >>> 1;
	 w16p =	w16p >>> 1;
	 w17  = w17  >>> 1;
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
