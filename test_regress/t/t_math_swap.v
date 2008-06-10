// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [31:0]  Operand1 = crc[31:0];
   wire [15:0]  Operand2 = crc[47:32];
   wire 	Unsigned = crc[48];
   reg 		rst;

   parameter wl = 16;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [wl-1:0]	Quotient;		// From test of Test.v
   wire [wl-1:0]	Remainder;		// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .Quotient			(Quotient[wl-1:0]),
	      .Remainder		(Remainder[wl-1:0]),
	      // Inputs
	      .Operand1			(Operand1[wl*2-1:0]),
	      .Operand2			(Operand2[wl-1:0]),
	      .clk			(clk),
	      .rst			(rst),
	      .Unsigned			(Unsigned));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, Quotient, Remainder};

   // What checksum will we end up with
`define EXPECTED_SUM 64'h98d41f89a8be5693

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x it=%x\n",$time, cyc, crc, result, test.Iteration);
`endif
      cyc <= cyc + 1;
      if (cyc < 20 || test.Iteration==4'd15) begin
	 crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      end
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
	 rst <= 1'b1;
      end
      else if (cyc<20) begin
	 sum <= 64'h0;
	 rst <= 1'b0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'h8dd70a44972ad809) $stop;
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test(clk, rst, Operand1, Operand2, Unsigned, Quotient, Remainder);

   parameter wl = 16;

   input [wl*2-1:0] Operand1;
   input [wl-1:0] Operand2;
   input clk, rst, Unsigned;
   output [wl-1:0] Quotient, Remainder;

   reg Cy, Overflow, Sign1, Sign2, Zero, Negative;
   reg [wl-1:0] ah,al,Quotient, Remainder;
   reg [3:0] 	Iteration;
   reg [wl-1:0] sub_quot,op;
   reg 		ah_ext;

   reg [1:0]	a,b,c,d,e;

   always @(posedge clk) begin
      if (!rst) begin
	 {a,b,c,d,e} = Operand1[9:0];
	 {a,b,c,d,e} = {e,d,c,b,a};
	 if (a != Operand1[1:0]) $stop;
	 if (b != Operand1[3:2]) $stop;
	 if (c != Operand1[5:4]) $stop;
	 if (d != Operand1[7:6]) $stop;
	 if (e != Operand1[9:8]) $stop;
      end
   end

   always @(posedge clk) begin
      if (rst) begin
	 Iteration <= 0;
         Quotient <= 0;
         Remainder <= 0;
      end
      else begin
	 if (Iteration == 0) begin
            {ah,al} = Operand1;
            op = Operand2;
            Cy = 0;
            Overflow = 0;
            Sign1 = (~Unsigned)&ah[wl-1];
            Sign2 = (~Unsigned)&(ah[wl-1]^op[wl-1]);
            if (Sign1) {ah,al} = -{ah,al};
	 end
`define BUG1
`ifdef BUG1
	 {ah_ext,ah,al} = {ah,al,Cy};
`else
	 ah_ext = ah[15];
	 ah[15:1] = ah[14:0];
	 ah[0] = al[15];
	 al[15:1] = al[14:0];
	 al[0] = Cy;
`endif
`ifdef TEST_VERBOSE
	 $display("%x %x %x %x %x %x %x %x %x",
		  Iteration, ah, al, Quotient, Remainder, Overflow, ah_ext, sub_quot, Cy);
`endif
	 {Cy,sub_quot} = (~Unsigned)&op[wl-1]? {ah_ext,ah}+op : {ah_ext,ah} - {1'b1,op};
	 if (Cy)
	   begin
              {ah_ext,ah} = {1'b0,sub_quot};
	   end
	 if (Iteration != 15 )
	   begin
              if (ah_ext) Overflow = 1;
	   end
	 else
	   begin
              if (al[14] && ~Unsigned) Overflow = 1;
              Quotient <= Sign2 ? -{al[14:0],Cy} : {al[14:0],Cy};
              Remainder <= Sign1 ? -ah : ah;
              if (Overflow)
		begin
	           Quotient <= Sign2 ? 16'h8001 : {Unsigned,{15{1'b1}}};
	           Remainder <= Unsigned ? 16'hffff : 16'h8000;
	           Zero = 1;
	           Negative = 1;
		end
	   end
	 Iteration <= Iteration + 1; // Count number of times this instruction is repeated
      end
   end

endmodule
