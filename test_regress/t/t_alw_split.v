// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   reg [15:0] m_din;

   // OK
   reg [15:0] a_split_1, a_split_2;
   always @ (/*AS*/m_din) begin
      a_split_1 = m_din;
      a_split_2 = m_din;
   end

   // OK
   reg [15:0] b_split_1, b_split_2;
   always @ (/*AS*/m_din) begin
      b_split_1 = m_din;
      b_split_2 = b_split_1;
   end

   // Not OK
   reg [15:0] c_split_1, c_split_2;
   always @ (/*AS*/m_din) begin
      c_split_1 = m_din;
      c_split_2 = c_split_1;
      c_split_1 = ~m_din;
   end

   // OK
   reg [15:0] d_split_1, d_split_2;
   always @ (posedge clk) begin
      d_split_1 <= m_din;
      d_split_2 <= d_split_1;
      d_split_1 <= ~m_din;
   end

   // Not OK
   always @ (posedge clk) begin
      $write(" foo %x", m_din);
      $write(" bar %x\n", m_din);
   end

   // Not OK
   reg [15:0] e_split_1, e_split_2;
   always @ (posedge clk) begin
      e_split_1 = m_din;
      e_split_2 = e_split_1;
   end

   // Not OK
   reg [15:0] f_split_1, f_split_2;
   always @ (posedge clk) begin
      f_split_2 = f_split_1;
      f_split_1 = m_din;
   end

   // Not Ok
   reg [15:0] l_split_1, l_split_2;
   always @ (posedge clk) begin
      l_split_2 <= l_split_1;
      l_split_1 <= l_split_2 | m_din;
   end

   // OK
   reg [15:0] z_split_1, z_split_2;
   always @ (posedge clk) begin
      z_split_1 <= 0;
      z_split_1 <= ~m_din;
   end
   always @ (posedge clk) begin
      z_split_2 <= 0;
      z_split_2 <= z_split_1;
   end

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
	    if (!(b_split_1==16'hfeed && b_split_2==16'hfeed)) $stop;
	    if (!(c_split_1==16'h0112 && c_split_2==16'hfeed)) $stop;
	    if (!(d_split_1==16'h0112 && d_split_2==16'h0112)) $stop;
	    if (!(e_split_1==16'hfeed && e_split_2==16'hfeed)) $stop;
	    if (!(f_split_1==16'hfeed && f_split_2==16'hfeed)) $stop;
	    if (!(z_split_1==16'h0112 && z_split_2==16'h0112)) $stop;
	 end
	 if (cyc==5) begin
	    m_din <= 16'he22e;
	    if (!(a_split_1==16'he11e && a_split_2==16'he11e)) $stop;
	    if (!(b_split_1==16'he11e && b_split_2==16'he11e)) $stop;
	    if (!(c_split_1==16'h1ee1 && c_split_2==16'he11e)) $stop;
	    if (!(d_split_1==16'h0112 && d_split_2==16'h0112)) $stop;
	    if (!(z_split_1==16'h0112 && z_split_2==16'h0112)) $stop;
	    // Two valid orderings, as we don't know which posedge clk gets evaled first
	    if (!(e_split_1==16'hfeed && e_split_2==16'hfeed) && !(e_split_1==16'he11e && e_split_2==16'he11e)) $stop;
	    if (!(f_split_1==16'hfeed && f_split_2==16'hfeed) && !(f_split_1==16'he11e && f_split_2==16'hfeed)) $stop;
	 end
	 if (cyc==6) begin
	    m_din <= 16'he33e;
	    if (!(a_split_1==16'he22e && a_split_2==16'he22e)) $stop;
	    if (!(b_split_1==16'he22e && b_split_2==16'he22e)) $stop;
	    if (!(c_split_1==16'h1dd1 && c_split_2==16'he22e)) $stop;
	    if (!(d_split_1==16'h1ee1 && d_split_2==16'h0112)) $stop;
	    if (!(z_split_1==16'h1ee1 && d_split_2==16'h0112)) $stop;
	    // Two valid orderings, as we don't know which posedge clk gets evaled first
	    if (!(e_split_1==16'he11e && e_split_2==16'he11e) && !(e_split_1==16'he22e && e_split_2==16'he22e)) $stop;
	    if (!(f_split_1==16'he11e && f_split_2==16'hfeed) && !(f_split_1==16'he22e && f_split_2==16'he11e)) $stop;
	 end
	 if (cyc==7) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
