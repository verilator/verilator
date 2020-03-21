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
   integer cyc; initial cyc=1;

   reg [15:0] m_din;

   // We expect all these blocks should split;
   // blocks that don't split should go in t_alw_nosplit.v

   reg [15:0] a_split_1, a_split_2;
   always @ (/*AS*/m_din) begin
      a_split_1 = m_din;
      a_split_2 = m_din;
   end

   reg [15:0] d_split_1, d_split_2;
   always @ (posedge clk) begin
      d_split_1 <= m_din;
      d_split_2 <= d_split_1;
      d_split_1 <= ~m_din;
   end

   reg [15:0] h_split_1;
   reg [15:0] h_split_2;
   always @ (posedge clk) begin
//      $write(" cyc = %x  m_din = %x\n", cyc, m_din);
      if (cyc > 2) begin
         if (m_din == 16'h0) begin
            h_split_1 <= 16'h0;
            h_split_2 <= 16'h0;
         end
         else begin
            h_split_1 <= m_din;
            h_split_2 <= ~m_din;
         end
      end
      else begin
         h_split_1 <= 16'h0;
         h_split_2 <= 16'h0;
      end
   end

   // (The checker block is an exception, it won't split.)
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc<=cyc+1;
	 if (cyc==1) begin
	    m_din <= 16'hfeed;
	 end
	 if (cyc==3) begin
	 end
	 if (cyc==4) begin
	    m_din <= 16'he11e;
	    //$write(" A %x %x\n", a_split_1, a_split_2);
	    if (!(a_split_1==16'hfeed && a_split_2==16'hfeed)) $stop;
	    if (!(d_split_1==16'h0112 && d_split_2==16'h0112)) $stop;
            if (!(h_split_1==16'hfeed && h_split_2==16'h0112)) $stop;
	 end
	 if (cyc==5) begin
	    m_din <= 16'he22e;
	    if (!(a_split_1==16'he11e && a_split_2==16'he11e)) $stop;
	    if (!(d_split_1==16'h0112 && d_split_2==16'h0112)) $stop;
            if (!(h_split_1==16'hfeed && h_split_2==16'h0112)) $stop;
	 end
	 if (cyc==6) begin
	    m_din <= 16'he33e;
	    if (!(a_split_1==16'he22e && a_split_2==16'he22e)) $stop;
	    if (!(d_split_1==16'h1ee1 && d_split_2==16'h0112)) $stop;
            if (!(h_split_1==16'he11e && h_split_2==16'h1ee1)) $stop;
	 end
	 if (cyc==7) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end  // always @ (posedge clk)

endmodule
