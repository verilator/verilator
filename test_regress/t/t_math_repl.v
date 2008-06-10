// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   reg [63:0] rf;
   reg [63:0] rf2;
   reg [63:0] biu;
   reg	      okidoki;

   always @* begin
      rf[63:32] = biu[63:32] & {32{okidoki}};
      rf[31:0]  = {32{okidoki}};
      rf2 = rf;
      rf2[31:0]  = ~{32{okidoki}};
   end

   reg  [31:0] src1, src0, sr, mask;
   wire [31:0] dualasr
	       = ((| src1[31:4])
		  ? {{16{src0[31]}}, {16{src0[15]}}}
		  : (  (  sr & {2{mask[31:16]}})
		       | (  {{16{src0[31]}}, {16{src0[15]}}}
			    & {2{~mask[31:16]}})));

   wire [31:0] sl_mask
	       = (32'hffffffff << src1[4:0]);

   wire [31:0] sr_mask
	       = {sl_mask[0],  sl_mask[1],
		  sl_mask[2],  sl_mask[3],  sl_mask[4],
                  sl_mask[5],  sl_mask[6],  sl_mask[7],
		  sl_mask[8],  sl_mask[9],
                  sl_mask[10], sl_mask[11],
		  sl_mask[12], sl_mask[13], sl_mask[14],
                  sl_mask[15], sl_mask[16],
		  sl_mask[17], sl_mask[18], sl_mask[19],
                  sl_mask[20], sl_mask[21],
		  sl_mask[22], sl_mask[23], sl_mask[24],
                  sl_mask[25], sl_mask[26],
		  sl_mask[27], sl_mask[28], sl_mask[29],
                  sl_mask[30], sl_mask[31]};

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
`ifdef TEST_VERBOSE
	 $write("%x %x %x %x %x\n", rf, rf2, dualasr, sl_mask, sr_mask);
`endif
	 if (cyc==1) begin
	    biu <= 64'h12451282_abadee00;
	    okidoki <= 1'b0;
	    src1 <= 32'h00000001;
	    src0 <= 32'h9a4f1235;
	    sr   <= 32'h0f19f567;
	    mask <= 32'h7af07ab4;
	 end
	 if (cyc==2) begin
	    biu <= 64'h12453382_abad8801;
	    okidoki <= 1'b1;
	    if (rf != 64'h0) $stop;
	    if (rf2 != 64'h00000000ffffffff) $stop;
	    src1 <= 32'h0010000f;
	    src0 <= 32'h028aa336;
	    sr   <= 32'h42ad0377;
	    mask <= 32'h1ab3b906;
	    if (dualasr != 32'h8f1f7060) $stop;
	    if (sl_mask != 32'hfffffffe) $stop;
	    if (sr_mask != 32'h7fffffff) $stop;
	 end
	 if (cyc==3) begin
	    biu <= 64'h12422382_77ad8802;
	    okidoki <= 1'b1;
	    if (rf != 64'h12453382ffffffff) $stop;
	    if (rf2 != 64'h1245338200000000) $stop;
	    src1 <= 32'h0000000f;
	    src0 <= 32'h5c158f71;
	    sr   <= 32'h7076c40a;
	    mask <= 32'h33eb3d44;
	    if (dualasr != 32'h0000ffff) $stop;
	    if (sl_mask != 32'hffff8000) $stop;
	    if (sr_mask != 32'h0001ffff) $stop;
	 end
	 if (cyc==4) begin
	    if (rf != 64'h12422382ffffffff) $stop;
	    if (rf2 != 64'h1242238200000000) $stop;
	    if (dualasr != 32'h3062cc1e) $stop;
	    if (sl_mask != 32'hffff8000) $stop;
	    if (sr_mask != 32'h0001ffff) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
