// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003-2007 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   reg [15:0] m_din;

   // OK
   reg [15:0] c_split_1, c_split_2, c_split_3, c_split_4, c_split_5;
   always @ (posedge clk) begin
      if (cyc==0) begin
	 /*AUTORESET*/
	 // Beginning of autoreset for uninitialized flops
	 c_split_1 <= 16'h0;
	 c_split_2 <= 16'h0;
	 c_split_3 <= 16'h0;
	 c_split_4 <= 0;
	 c_split_5 <= 0;
	 // End of automatics
      end
      else begin
	 c_split_1 <= m_din;
	 c_split_2 <= c_split_1;
	 c_split_3 <= c_split_2 & {16{(cyc!=0)}};
	 if (cyc==1) begin
	    c_split_4 <= 16'h4;
	    c_split_5 <= 16'h5;
	 end
	 else begin
	    c_split_4 <= c_split_3;
	    c_split_5 <= c_split_4;
	 end
      end
   end

   // OK
   reg [15:0] d_split_1, d_split_2;
   always @ (posedge clk) begin
      if (cyc==0) begin
	 /*AUTORESET*/
	 // Beginning of autoreset for uninitialized flops
	 d_split_1 <= 16'h0;
	 d_split_2 <= 16'h0;
	 // End of automatics
      end
      else begin
	 d_split_1 <= m_din;
	 d_split_2 <= d_split_1;
	 d_split_1 <= ~m_din;
      end
   end

   // Not OK
   always @ (posedge clk) begin
      if (cyc==0) begin
	 /*AUTORESET*/
	 // Beginning of autoreset for uninitialized flops
	 // End of automatics
      end
      else begin
	 $write(" foo %x", m_din);
	 $write(" bar %x\n", m_din);
      end
   end

   // Not OK
   reg [15:0] e_split_1, e_split_2;
   always @ (posedge clk) begin
      if (cyc==0) begin
	 /*AUTORESET*/
	 // Beginning of autoreset for uninitialized flops
	 e_split_1 = 16'h0;
	 e_split_2 = 16'h0;
	 // End of automatics
      end
      else begin
	 e_split_1 = m_din;
	 e_split_2 = e_split_1;
      end
   end

   // Not OK
   reg [15:0] f_split_1, f_split_2;
   always @ (posedge clk) begin
      if (cyc==0) begin
	 /*AUTORESET*/
	 // Beginning of autoreset for uninitialized flops
	 f_split_1 = 16'h0;
	 f_split_2 = 16'h0;
	 // End of automatics
      end
      else begin
	 f_split_2 = f_split_1;
	 f_split_1 = m_din;
      end
   end

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 //$write(" C %d %x %x\n", cyc, c_split_1, c_split_2);
	 cyc<=cyc+1;
	 if (cyc==1) begin
	    m_din <= 16'hfeed;
	 end
	 if (cyc==3) begin
	 end
	 if (cyc==4) begin
	    m_din <= 16'he11e;
	    if (!(d_split_1==16'h0112 && d_split_2==16'h0112)) $stop;
	    if (!(e_split_1==16'hfeed && e_split_2==16'hfeed)) $stop;
	    if (!(f_split_1==16'hfeed && f_split_2==16'hfeed)) $stop;
	 end
	 if (cyc==5) begin
	    m_din <= 16'he22e;
	    if (!(d_split_1==16'h0112 && d_split_2==16'h0112)) $stop;
	    // Two valid orderings, as we don't know which posedge clk gets evaled first
	    if (!(e_split_1==16'hfeed && e_split_2==16'hfeed) && !(e_split_1==16'he11e && e_split_2==16'he11e)) $stop;
	    if (!(f_split_1==16'hfeed && f_split_2==16'hfeed) && !(f_split_1==16'he11e && f_split_2==16'hfeed)) $stop;
	 end
	 if (cyc==6) begin
	    m_din <= 16'he33e;
	    if (!(c_split_1==16'he11e && c_split_2==16'hfeed && c_split_3==16'hfeed)) $stop;
	    if (!(d_split_1==16'h1ee1 && d_split_2==16'h0112)) $stop;
	    // Two valid orderings, as we don't know which posedge clk gets evaled first
	    if (!(e_split_1==16'he11e && e_split_2==16'he11e) && !(e_split_1==16'he22e && e_split_2==16'he22e)) $stop;
	    if (!(f_split_1==16'he11e && f_split_2==16'hfeed) && !(f_split_1==16'he22e && f_split_2==16'he11e)) $stop;
	 end
	 if (cyc==7) begin
	    m_din <= 16'he44e;
	    if (!(c_split_1==16'he22e && c_split_2==16'he11e && c_split_3==16'hfeed)) $stop;
	 end
	 if (cyc==8) begin
	    m_din <= 16'he55e;
	    if (!(c_split_1==16'he33e && c_split_2==16'he22e && c_split_3==16'he11e
		  && c_split_4==16'hfeed && c_split_5==16'hfeed)) $stop;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
