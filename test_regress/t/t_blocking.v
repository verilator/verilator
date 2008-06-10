// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer _mode;  initial _mode=0;
   reg [7:0] a;
   reg [7:0] b;
   reg [7:0] c;

   reg [7:0] mode_d1r;
   reg [7:0] mode_d2r;
   reg [7:0] mode_d3r;

   // surefire lint_off ITENST
   // surefire lint_off STMINI
   // surefire lint_off NBAJAM

   always @ (posedge clk) begin	// filp-flops with asynchronous reset
      if (0) begin
	 _mode <= 0;
      end
      else begin
	 _mode <= _mode + 1;
	 if (_mode==0) begin
	    $write("[%0t] t_blocking: Running\n", $time);
	    a <= 8'd0;
	    b <= 8'd0;
	    c <= 8'd0;
	 end
	 else if (_mode==1) begin
	    if (a !== 8'd0) $stop;
	    if (b !== 8'd0) $stop;
	    if (c !== 8'd0) $stop;
	    a <= b;
	    b <= 8'd1;
	    c <= b;
	    if (a !== 8'd0) $stop;
	    if (b !== 8'd0) $stop;
	    if (c !== 8'd0) $stop;
	 end
	 else if (_mode==2) begin
	    if (a !== 8'd0) $stop;
	    if (b !== 8'd1) $stop;
	    if (c !== 8'd0) $stop;
	    a <= b;
	    b <= 8'd2;
	    c <= b;
	    if (a !== 8'd0) $stop;
	    if (b !== 8'd1) $stop;
	    if (c !== 8'd0) $stop;
	 end
	 else if (_mode==3) begin
	    if (a !== 8'd1) $stop;
	    if (b !== 8'd2) $stop;
	    if (c !== 8'd1) $stop;
	 end
	 else if (_mode==4) begin
	    if (mode_d3r != 8'd1) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

   always @ (posedge clk) begin
      mode_d3r <= mode_d2r;
      mode_d2r <= mode_d1r;
      mode_d1r <= _mode[7:0];
   end

   reg [14:10] bits;
   // surefire lint_off SEQASS
   always @ (posedge clk) begin
      if (_mode==1) begin
	 bits[14:13] <= 2'b11;
	 bits[12] <= 1'b1;
      end
      if (_mode==2) begin
	 bits[11:10] <= 2'b10;
	 bits[13] <= 0;
      end
      if (_mode==3) begin
	 if (bits !== 5'b10110) $stop;
      end
   end

endmodule
