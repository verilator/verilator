// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [15:0] l;
   reg [49:0] q;
   reg [79:0] w;
   reg [4:0]  lc;
   reg 	      lo;
   reg 	      l0;
   reg [5:0]  qc;
   reg 	      qo;
   reg 	      q0;
   reg [6:0]  wc;
   reg 	      wo;
   reg 	      w0;

   always @* begin
      lc = $countones(l);
      lo = $onehot(l);
      l0 = $onehot0(l);
      wc = $countones(w);
      wo = $onehot(w);
      w0 = $onehot0(w);
      qc = $countones(q);
      qo = $onehot(q);
      q0 = $onehot0(q);
   end

   integer cyc; initial cyc=1;
   integer cyc_com;
   always_comb begin
      cyc_com = cyc;
   end

   integer cyc_d1;
   always_ff @ (posedge clk) begin
      cyc_d1 <= cyc_com;
   end

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 //$write("%d %x %d %x %x   %x %d %x %x  %x %d %x %x\n",
	 //	cyc, l, lc, lo, l0,   q,qc,qo,q0,  w,wc,wo,w0);
	 if (cyc_com != cyc_com) $stop;
	 if (cyc_d1 != cyc-1) $stop;
	 if (cyc==0) begin
	    // Constification check
	    if ($countones(32'b11001011101) != 7) $stop;
	    if ($countones(32'b0) != 0) $stop;
	    if ($isunknown(32'b11101x11111) != 1) $stop;
	    if ($isunknown(32'b11101011111) != 0) $stop;
	    if ($isunknown(32'b10zzzzzzzzz) != 0) $stop;
	    if ($bits(0) != 32'd32) $stop;
	    if ($bits(lc) != 5) $stop;
	    if ($onehot(32'b00000001000000) != 1'b1) $stop;
	    if ($onehot(32'b00001001000000) != 1'b0) $stop;
	    if ($onehot(32'b0) != 1'b0) $stop;
	    if ($onehot0(32'b00000001000000) != 1'b1) $stop;
	    if ($onehot0(32'b00001001000000) != 1'b0) $stop;
	    if ($onehot0(32'b0) != 1'b1) $stop;
	 end
	 if (cyc==1) begin
	    l <= 16'b0;
	    q <= 50'h0;
	    w <= 80'h0;
	 end
	 if (cyc==2) begin
	    l <= ~16'b0;
	    q <= ~50'h0;
	    w <= ~80'h0;
	    //
	    if ({lc,lo,l0} != {5'd0,1'b0,1'b1}) $stop;
	    if ({qc,qo,q0} != {6'd0,1'b0,1'b1}) $stop;
	    if ({wc,wo,w0} != {7'd0,1'b0,1'b1}) $stop;
	 end
	 if (cyc==3) begin
	    l <= 16'b0010110010110111;
	    q <= 50'h01_1111_0001;
	    w <= 80'h0100_0000_0f00_00f0_0000;
	    //
	    if ({lc,lo,l0} != {5'd16,1'b0,1'b0}) $stop;
	    if ({qc,qo,q0} != {6'd50,1'b0,1'b0}) $stop;
	    if ({wc,wo,w0} != {7'd80,1'b0,1'b0}) $stop;
	 end
	 if (cyc==4) begin
	    l <= 16'b0000010000000000;
	    q <= 50'h1_0000_0000;
	    w <= 80'h010_00000000_00000000;
	    //
	    if ({lc,lo,l0} != {5'd9,1'b0,1'b0}) $stop;
	    if ({qc,qo,q0} != {6'd6,1'b0,1'b0}) $stop;
	    if ({wc,wo,w0} != {7'd9,1'b0,1'b0}) $stop;
	 end
	 if (cyc==5) begin
	    l <= 16'b0000000100000000;
	    q <= 50'h8000_0000_0000;
	    w <= 80'h10_00000000_00000000;
	    //
	    if ({lc,lo,l0} != {5'd1,1'b1,1'b1}) $stop;
	    if ({qc,qo,q0} != {6'd1,1'b1,1'b1}) $stop;
	    if ({wc,wo,w0} != {7'd1,1'b1,1'b1}) $stop;
	 end
	 if (cyc==6) begin
	    l <= 16'b0000100100000000;
	    q <= 50'h01_00000100;
	    w <= 80'h01_00000100_00000000;
	    //
	    if ({lc,lo,l0} != {5'd1,1'b1,1'b1}) $stop;
	    if ({qc,qo,q0} != {6'd1,1'b1,1'b1}) $stop;
	    if ({wc,wo,w0} != {7'd1,1'b1,1'b1}) $stop;
	 end
	 if (cyc==7) begin
	    //
	    if ({lc,lo,l0} != {5'd2,1'b0,1'b0}) $stop;
	    if ({qc,qo,q0} != {6'd2,1'b0,1'b0}) $stop;
	    if ({wc,wo,w0} != {7'd2,1'b0,1'b0}) $stop;
	 end
	 if (cyc==8) begin
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

   final begin
      $write("Goodbye world, at cycle %0d\n", cyc);
   end

endmodule
