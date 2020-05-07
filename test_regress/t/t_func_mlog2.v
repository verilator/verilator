// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003-2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   integer cyc; initial cyc=1;
   integer sum;
   integer cpre;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cpre = cyc;
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    if (mlog2(32'd0) != 32'd0) $stop;
	    if (mlog2(32'd1) != 32'd0) $stop;
	    if (mlog2(32'd3) != 32'd2) $stop;
	    sum <= 32'd0;
	 end
	 else if (cyc<90) begin
	    // (cyc) so if we trash the variable things will get upset.
	    sum <= mlog2(cyc) + sum * 32'd42;
	    if (cpre != cyc) $stop;
	 end
	 else if (cyc==90) begin
	    if (sum !== 32'h0f12bb51) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

   function integer mlog2;
      input [31:0] value;
      integer 	   i;
      begin
	 if(value < 32'd1) begin
            mlog2 = 0;
	 end
	 else begin
            value = value - 32'd1;
            mlog2 = 0;
            for(i=0;i<32;i=i+1) begin
               if(value > 32'd0) begin
                  mlog2 = mlog2 + 1;
               end
               value = value >> 1;
            end
	 end
      end
   endfunction

endmodule
