// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   wire [1:0] 	a = crc[1 +: 2];
   wire [1:0] 	b = crc[3 +: 2];
   wire [1:0] 	c = crc[5 +: 2];
   wire [1:0] 	d = crc[7 +: 2];
   wire [1:0] 	e = crc[9 +: 2];
   wire [1:0] 	f = crc[11+: 2];
   wire [1:0] 	g = crc[13+: 2];

   //	left	() [] :: .
   //	unary	+ - ! ~ & ~& | ~| ^ ~^ ^~ ++ -- (unary)
   //	left	**
   //	left	* / %
   //	left	+ - (binary)
   //	left	<< >> <<< >>>
   //	left	< <= > >= inside dist
   //	left	== != === !== ==? !=?
   //	left	& (binary)
   //	left	^ ~^ ^~ (binary)
   //	left	| (binary)
   //	left	&&
   //	left	||
   //	left	? :
   //	right	->
   //	none	= += -= *= /= %= &= ^= |= <<= >>= <<<= >>>= := :/ <=
   //		{} {{}} concatenation

   wire [1:0] 	bnz = (b==2'b0) ? 2'b11 : b;
   wire [1:0] 	cnz = (c==2'b0) ? 2'b11 : c;
   wire [1:0] 	dnz = (d==2'b0) ? 2'b11 : d;
   wire [1:0] 	enz = (e==2'b0) ? 2'b11 : e;

   // verilator lint_off WIDTH
   // Do a few in each group
   wire [1:0] o1 = ~ a;  // Can't get more than one reduction to parse
   wire [1:0] o2 = ^ b;  // Can't get more than one reduction to parse
   wire [1:0] o3 = a ** b ** c;  // Some simulators botch this

   wire [1:0] o4 = a * b / cnz % dnz * enz;
   wire [1:0] o5 = a + b - c + d;
   wire [1:0] o6 = a << b >> c <<< d >>> e <<< f;
   wire [1:0] o7 = a < b <= c;
   wire [1:0] o8 = a == b != c === d == e;
   wire [1:0] o9 = a & b & c;
   wire [1:0] o10 = a ^ b ~^ c ^~ d ^ a;
   wire [1:0] o11 = a | b | c;
   wire [1:0] o12 = a && b && c;
   wire [1:0] o13 = a || b || c;
   wire [1:0] o14 = a ? b ? c : d : e;
   wire [1:0] o15 = a ? b : c ? d : e;

   // Now cross each pair of groups
   wire [1:0] x1 = ~ a ** ~ b ** ~c;  // Some simulators botch this
   wire [1:0] x2 = a ** b * c ** d;  // Some simulators botch this
   wire [1:0] x3 = a + b * c + d;
   wire [1:0] x4 = a + b << c + d;
   wire [1:0] x5 = a == b << c == d;
   wire [1:0] x6 = a & b << c & d;
   wire [1:0] x7 = a ^ b & c ^ d;
   wire [1:0] x8 = a | b ^ c | d;
   wire [1:0] x9 = a && b | c && d;
   wire [1:0] x10 = a || b && c || d;
   wire [1:0] x11 = a ? b || c : d ? e : f;

   // verilator lint_on WIDTH

   function [1:0] pow (input [1:0] x, input [1:0] y);
      casez ({x,y})
	4'b00_??: pow = 2'b00;
	4'b01_00: pow = 2'b01;
	4'b01_01: pow = 2'b01;
	4'b01_10: pow = 2'b01;
	4'b01_11: pow = 2'b01;
	4'b10_00: pow = 2'b01;
	4'b10_01: pow = 2'b10;
	4'b10_10: pow = 2'b00;
	4'b10_11: pow = 2'b00;
	4'b11_00: pow = 2'b01;
	4'b11_01: pow = 2'b11;
	4'b11_10: pow = 2'b01;
	4'b11_11: pow = 2'b11;
      endcase
   endfunction

   // Aggregate outputs into a single result vector
   wire [63:0] result = {12'h0,
			 x11,x10,x9,x8,x7,x6,x5,x4,x3,x2,x1,
			 o15,o14,o13,o12,o11,o10,o9,o8,o7,o6,o5,o4,o3,o2,o1};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x ",$time, cyc, crc, result);
      $write(" %b",o1);
      $write(" %b",o2);
      $write(" %b",o3);
      $write(" %b",o4);
      $write(" %b",o5);
      $write(" %b",o6);
      $write(" %b",o7);
      $write(" %b",o8);
      $write(" %b",o9);
      $write(" %b",o10);
      $write(" %b",o11);
      $write(" %b",o12);
      $write(" %b",o13);
      $write(" %b",o14);
      $write(" %b",o15);
      // Now cross each pair of groups
      $write(" %b",x1);
      $write(" %b",x2);
      $write(" %b",x3);
      $write(" %b",x4);
      $write(" %b",x5);
      $write(" %b",x6);
      $write(" %b",x7);
      $write(" %b",x8);
      $write(" %b",x9);
      $write(" %b",x10);
      $write(" %b",x11);
      $write("\n");
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
	 sum <= 64'h0;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h2756ea365ec7520e
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
