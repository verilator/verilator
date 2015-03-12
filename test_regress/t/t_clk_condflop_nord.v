// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (clk);
   input clk;

   reg [0:0] d1;
   reg [2:0] d3;
   reg [7:0] d8;

   wire [0:0] q1;
   wire [2:0] q3;
   wire [7:0] q8;

   // verilator lint_off UNOPTFLAT
   reg 	      ena;
   // verilator lint_on  UNOPTFLAT

   condff #(12) condff
     (.clk(clk), .sen(1'b0), .ena(ena),
      .d({d8,d3,d1}),
      .q({q8,q3,q1}));

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 //$write("%x %x %x %x\n", cyc, q8, q3, q1);
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    d1 <= 1'b1; d3<=3'h1; d8<=8'h11;
	    ena <= 1'b1;
	 end
	 if (cyc==2) begin
	    d1 <= 1'b0; d3<=3'h2; d8<=8'h33;
	    ena <= 1'b0;
	 end
	 if (cyc==3) begin
	    d1 <= 1'b1; d3<=3'h3; d8<=8'h44;
	    ena <= 1'b1;
	    if (q8 != 8'h11) $stop;
	 end
	 if (cyc==4) begin
	    d1 <= 1'b1; d3<=3'h4; d8<=8'h77;
	    ena <= 1'b1;
	    if (q8 != 8'h11) $stop;
	 end
	 if (cyc==5) begin
	    d1 <= 1'b1; d3<=3'h0; d8<=8'h88;
	    ena <= 1'b1;
	    if (q8 != 8'h44) $stop;
	 end
	 if (cyc==6) begin
	    if (q8 != 8'h77) $stop;
	 end
	 if (cyc==7) begin
	    if (q8 != 8'h88) $stop;
	 end
	 //
	 if (cyc==20) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule

module condff (clk, sen, ena, d, q);
   parameter WIDTH = 1;
   input     clk;

   input     sen;
   input     ena;
   input [WIDTH-1:0] d;
   output [WIDTH-1:0] q;

   condffimp #(.WIDTH(WIDTH))
     imp (.clk(clk), .sen(sen), .ena(ena), .d(d), .q(q));
endmodule

module condffimp (clk, sen, ena, d, q);
   parameter WIDTH = 1;
   input     clk;
   input     sen;
   input     ena;
   input [WIDTH-1:0] d;
   output reg [WIDTH-1:0] q;
   wire   gatedclk;

   clockgate clockgate (.clk(clk), .sen(sen), .ena(ena), .gatedclk(gatedclk));

   always @(posedge gatedclk) begin
      if (gatedclk === 1'bX) begin
	 q <= {WIDTH{1'bX}};
      end
      else begin
	 q <= d;
      end
   end

endmodule

module clockgate (clk, sen, ena, gatedclk);
   input	clk;
   input	sen;
   input	ena;
   output	gatedclk;

   reg		ena_b;
   wire gatedclk = clk & ena_b;

   // verilator lint_off COMBDLY
   always @(clk or ena or sen) begin
      if (~clk) begin
        ena_b <= ena | sen;
      end
      else begin
	 if ((clk^sen)===1'bX) ena_b <= 1'bX;
      end
   end
   // verilator lint_on COMBDLY

endmodule
