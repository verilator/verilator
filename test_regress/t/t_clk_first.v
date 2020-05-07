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
   reg 	 reset_l;

   int cyc;
   initial reset_l = 0;
   always @ (posedge clk) begin
      if (cyc==0) reset_l <= 1'b1;
      else if (cyc==1) reset_l <= 1'b0;
      else if (cyc==10) reset_l <= 1'b1;
   end

   t_clk t (/*AUTOINST*/
	    // Inputs
	    .clk			(clk),
	    .fastclk			(fastclk),
	    .reset_l			(reset_l));
endmodule

module t_clk (/*AUTOARG*/
   // Inputs
   clk, fastclk, reset_l
   );

   input clk;
   input fastclk;
   input reset_l;

   // surefire lint_off STMINI
   // surefire lint_off CWECSB
   // surefire lint_off NBAJAM
   reg 	  _ranit; initial _ranit=0;
   // surefire lint_off UDDSMX
   reg [7:0] clk_clocks; initial clk_clocks = 0; // surefire lint_off_line WRTWRT
   wire [7:0] clk_clocks_d1r;
   wire [7:0] clk_clocks_d1sr;
   wire [7:0] clk_clocks_cp2_d1r;
   wire [7:0] clk_clocks_cp2_d1sr;
   // verilator lint_off MULTIDRIVEN
   reg [7:0] int_clocks; initial int_clocks = 0;
   // verilator lint_on MULTIDRIVEN
   reg [7:0] int_clocks_copy;

   // verilator lint_off GENCLK
   reg 	     internal_clk; initial internal_clk = 0;
   reg 	     reset_int_;
   // verilator lint_on GENCLK

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] CLK1 %x\n", $time, reset_l);
`endif
      if (!reset_l) begin
	 clk_clocks <= 0;
	 int_clocks <= 0;
	 internal_clk <= 1'b1;
	 reset_int_ <= 0;
      end
      else begin
	 internal_clk <= ~internal_clk;
	 if (!_ranit) begin
	    _ranit <= 1;
`ifdef TEST_VERBOSE
	    $write("[%0t] t_clk: Running\n",$time);
`endif
	    reset_int_ <= 1;
	 end
      end
   end

   reg [7:0] sig_rst;
   always @ (posedge clk or negedge reset_l) begin
`ifdef TEST_VERBOSE
      $write("[%0t] CLK2 %x sr=%x\n", $time, reset_l, sig_rst);
`endif
      if (!reset_l) begin
	 sig_rst <= 0;
      end
      else begin
	 sig_rst <= sig_rst + 1; // surefire lint_off_line ASWIBB
      end
   end

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] CLK3 %x cc=%x sr=%x\n", $time, reset_l, clk_clocks, sig_rst);
`endif
      if (!reset_l) begin
	 clk_clocks <= 0;
      end
      else begin
	 clk_clocks <= clk_clocks + 8'd1;
	 if (clk_clocks == 4) begin
	    if (sig_rst !== 4) $stop;
	    if (clk_clocks_d1r !== 3) $stop;
	    if (int_clocks !== 2) $stop;
	    if (int_clocks_copy !== 2) $stop;
	    if (clk_clocks_d1r !== clk_clocks_cp2_d1r) $stop;
	    if (clk_clocks_d1sr !== clk_clocks_cp2_d1sr) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

   reg [7:0] resetted;
   always @ (posedge clk or negedge reset_int_) begin
`ifdef TEST_VERBOSE
      $write("[%0t] CLK4 %x\n", $time, reset_l);
`endif
      if (!reset_int_) begin
	 resetted <= 0;
      end
      else begin
	 resetted <= resetted + 8'd1;
      end
   end

   always @ (int_clocks) begin
      int_clocks_copy = int_clocks;
   end

   always @ (negedge internal_clk) begin
      int_clocks <= int_clocks + 8'd1;
   end

   t_clk_flop flopa (.clk(clk), .clk2(fastclk), .a(clk_clocks),
		     .q(clk_clocks_d1r), .q2(clk_clocks_d1sr));
   t_clk_flop flopb (.clk(clk), .clk2(fastclk), .a(clk_clocks),
		     .q(clk_clocks_cp2_d1r), .q2(clk_clocks_cp2_d1sr));
   t_clk_two two (/*AUTOINST*/
		  // Inputs
		  .fastclk		(fastclk),
		  .reset_l		(reset_l));

endmodule

module t_clk_flop (/*AUTOARG*/
   // Outputs
   q, q2,
   // Inputs
   clk, clk2, a
   );
   parameter WIDTH=8;
   input clk;
   input clk2;
   input [(WIDTH-1):0]  a;
   output [(WIDTH-1):0] q;
   output [(WIDTH-1):0] q2;
   reg [(WIDTH-1):0] q;
   reg [(WIDTH-1):0] q2;
   always @ (posedge clk) q<=a;
   always @ (posedge clk2) q2<=a;
endmodule

module t_clk_two (/*AUTOARG*/
   // Inputs
   fastclk, reset_l
   );
   input fastclk;
   input reset_l;
   // verilator lint_off GENCLK
   reg clk2;
   // verilator lint_on GENCLK
   reg [31:0] count;

   t_clk_twob tb (.*);

   wire reset_h = ~reset_l;
   always @ (posedge fastclk) begin
      if (reset_h) clk2 <= 0;
      else clk2 <= ~clk2;
   end
   always @ (posedge clk2) begin
      if (reset_h) count <= 0;
      else count <= count + 1;
   end
endmodule

module t_clk_twob (/*AUTOARG*/
   // Inputs
   fastclk, reset_l
   );
   input fastclk;
   input reset_l;

   always @ (posedge fastclk) begin
      // Extra line coverage point, just to make sure coverage
      // hierarchy under inlining lands properly
      if (reset_l) ;
   end
endmodule
