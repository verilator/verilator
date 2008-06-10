// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t_clk (/*AUTOARG*/
   // Outputs
   passed,
   // Inputs
   fastclk, clk, reset_l
   );

   input fastclk;
   input clk;
   input reset_l;
   output passed;  reg passed; initial passed = 0;
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
      //$write("CLK1 %x\n", reset_l);
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
	    $write("[%0t] t_clk: Running\n",$time);
	    reset_int_ <= 1;
	 end
      end
   end

   reg [7:0] sig_rst;
   always @ (posedge clk or negedge reset_l) begin
      //$write("CLK2 %x sr=%x\n", reset_l, sig_rst);
      if (!reset_l) begin
	 sig_rst <= 0;
      end
      else begin
	 sig_rst <= sig_rst + 1; // surefire lint_off_line ASWIBB
      end
   end

   always @ (posedge clk) begin
      //$write("CLK3 %x cc=%x sr=%x\n", reset_l, clk_clocks, sig_rst);
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
	    passed <= 1'b1;
	    $write("[%0t] t_clk: Passed\n",$time);
	 end
      end
   end

   reg [7:0] resetted;
   always @ (posedge clk or negedge reset_int_) begin
      //$write("CLK4 %x\n", reset_l);
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
