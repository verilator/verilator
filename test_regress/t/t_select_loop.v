// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   reg [255:0] 		a;
   reg [255:0] 		q;
   reg [63:0] 		qq;

   integer 		i;
   always @* begin
      for (i=0; i<256; i=i+1) begin
	 q[255-i] = a[i];
      end
      q[27:16] = 12'hfed;
      for (i=0; i<64; i=i+1) begin
	 qq[63-i] = a[i];
      end
      qq[27:16] = 12'hfed;
   end

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
`ifdef TEST_VERBOSE
	 $write("%x/%x %x\n", q, qq, a);
`endif
	 if (cyc==1) begin
	    a = 256'hed388e646c843d35de489bab2413d77045e0eb7642b148537491f3da147e7f26;
	 end
	 if (cyc==2) begin
	    a = 256'h0e17c88f3d5fe51a982646c8e2bd68c3e236ddfddddbdad20a48e039c9f395b8;
	    if (q != 256'h64fe7e285bcf892eca128d426ed707a20eebc824d5d9127bacbc21362fed1cb7) $stop;
	    if (qq != 64'h64fe7e285fed892e) $stop;
	 end
	 if (cyc==3) begin
	    if (q != 256'h1da9cf939c0712504b5bdbbbbfbb6c47c316bd471362641958a7fabcffede870) $stop;
	    if (qq != 64'h1da9cf939fed1250) $stop;
	 end
	 if (cyc==4) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
