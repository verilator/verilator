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

   reg posedge_wr_clocks;
   reg prev_wr_clocks;
   reg [31:0] m_din;
   reg [31:0] m_dout;

   always @(negedge clk) begin
      prev_wr_clocks = 0;
   end

   reg comb_pos_1;
   reg comb_prev_1;
   always @ (/*AS*/clk or posedge_wr_clocks or prev_wr_clocks) begin
      comb_pos_1 = (clk &~ prev_wr_clocks);
      comb_prev_1 = comb_pos_1 | posedge_wr_clocks;
      comb_pos_1 = 1'b1;
   end

   always @ (posedge clk) begin
      posedge_wr_clocks = (clk &~ prev_wr_clocks); //surefire lint_off_line SEQASS
      prev_wr_clocks = prev_wr_clocks | posedge_wr_clocks;	//surefire lint_off_line SEQASS
      if (posedge_wr_clocks) begin
	 //$write("[%0t] Wrclk\n", $time);
	 m_dout <= m_din;
      end
   end

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc<=cyc+1;
	 if (cyc==1) begin
	    $write("  %x\n",comb_pos_1);
	    m_din <= 32'hfeed;
	 end
	 if (cyc==2) begin
	    $write("  %x\n",comb_pos_1);
	    m_din <= 32'he11e;
	 end
	 if (cyc==3) begin
	    m_din <= 32'he22e;
	    $write("  %x\n",comb_pos_1);
	    if (m_dout!=32'hfeed) $stop;
	 end
	 if (cyc==4) begin
	    if (m_dout!=32'he11e) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
