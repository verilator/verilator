// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, fastclk
   );

   input clk;
   input fastclk;

   genvar unused;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire			o_com;			// From b of t_inst_first_b.v
   wire			o_seq_d1r;		// From b of t_inst_first_b.v
   // End of automatics

   integer _mode;  // initial _mode=0
   reg        na,nb,nc,nd,ne;
   wire       ma,mb,mc,md,me;
   wire       da,db,dc,dd,de;
   reg	[7:0] wa,wb,wc,wd,we;
   wire	[7:0] qa,qb,qc,qd,qe;

   wire	[5:0]  ra;
   wire	[4:0]  rb;
   wire	[29:0] rc;
   wire	[63:0] rd;
   reg	   [5:0]  sa;
   reg	   [4:0]  sb;
   reg	   [29:0] sc;
   reg	   [63:0] sd;

   reg 		_guard1; initial _guard1=0;
   wire [104:0] r_wide = {ra,rb,rc,rd};
   reg 		_guard2; initial _guard2=0;
   wire [98:0] 	r_wide0 = {rb,rc,rd};
   reg 		_guard3; initial _guard3=0;
   wire [93:0] 	r_wide1 = {rc,rd};
   reg 		_guard4; initial _guard4=0;
   wire [63:0] 	r_wide2 = {rd};
   reg 		_guard5; initial _guard5=0;
   wire [168:0] r_wide3 = {ra,rb,rc,rd,rd};
   reg [127:0]	_guard6; initial _guard6=0;

   t_inst_first_a a (
	       .clk		(clk),
	       // Outputs
	       .o_w5		({ma,mb,mc,md,me}),
	       .o_w5_d1r	({da,db,dc,dd,de}),
	       .o_w40		({qa,qb,qc,qd,qe}),
	       .o_w104		({ra,rb,rc,rd}),
	       // Inputs
	       .i_w5		({na,nb,nc,nd,ne}),
	       .i_w40		({wa,wb,wc,wd,we}),
	       .i_w104		({sa,sb,sc,sd})
	       );

   reg 		i_seq;
   reg		i_com;
   wire [15:14] o2_comhigh;

   t_inst_first_b b (
	       .o2_com			(o2_comhigh),
	       .i2_com			({i_com,~i_com}),
	       .wide_for_trace		(128'h1234_5678_aaaa_bbbb_cccc_dddd),
	       .wide_for_trace_2	(_guard6 + 128'h1234_5678_aaaa_bbbb_cccc_dddd),
	       /*AUTOINST*/
		     // Outputs
		     .o_seq_d1r		(o_seq_d1r),
		     .o_com		(o_com),
		     // Inputs
		     .clk		(clk),
		     .i_seq		(i_seq),
		     .i_com		(i_com));

   // surefire lint_off STMINI
   initial _mode = 0;

   always @ (posedge fastclk) begin
      if (_mode==1) begin
	 if (o_com !== ~i_com) $stop;
	 if (o2_comhigh !== {~i_com,i_com}) $stop;
      end
   end

   always @ (posedge clk) begin
      //$write("[%0t] t_inst: MODE = %0x  NA=%x MA=%x DA=%x\n", $time, _mode,
      //	     {na,nb,nc,nd,ne}, {ma,mb,mc,md,me}, {da,db,dc,dd,de});
      $write("[%0t] t_inst: MODE = %0x  IS=%x OS=%x\n", $time, _mode, i_seq, o_seq_d1r);
      if (_mode==0) begin
	 $write("[%0t] t_inst: Running\n", $time);
	 _mode<=1;
	 {na,nb,nc,nd,ne} <= 5'b10110;
	 {wa,wb,wc,wd,we} <= {8'ha, 8'hb, 8'hc, 8'hd, 8'he};
	 {sa,sb,sc,sd} <= {6'hf, 5'h3, 30'h12345, 32'h0abc_abcd, 32'h7654_3210};
	 //
	 i_seq <= 1'b1;
	 i_com <= 1'b1;
      end
      else if (_mode==1) begin
	 _mode<=2;
	 if ({ma,mb,mc,md,me} !== 5'b10110) $stop;
	 if ({qa,qb,qc,qd,qe} !== {8'ha,8'hb,8'hc,8'hd,8'he}) $stop;
	 if ({sa,sb,sc,sd} !== {6'hf, 5'h3, 30'h12345, 32'h0abc_abcd, 32'h7654_3210}) $stop;
      end
      else if (_mode==2) begin
	 _mode<=3;
	 if ({da,db,dc,dd,de} !== 5'b10110) $stop;
	 if (o_seq_d1r !== ~i_seq) $stop;
	 //
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
      if (|{_guard1,_guard2,_guard3,_guard4,_guard5,_guard6}) begin
	 $write("Guard error %x %x %x %x %x\n",_guard1,_guard2,_guard3,_guard4,_guard5);
	 $stop;
      end
   end

   // surefire lint_off UDDSDN
   wire _unused_ok = |{1'b1, r_wide0, r_wide1,r_wide2,r_wide3,r_wide};

endmodule
