// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] crc;
   reg [63:0] sum;

   wire [3:0] Value = crc[3:0];

   wire [3:0] Result;
   wire [3:0] Result2;

   Testit testit (/*AUTOINST*/
		  // Outputs
		  .Result		(Result[3:0]),
		  .Result2		(Result2[3:0]),
		  // Inputs
		  .clk			(clk),
		  .Value		(Value[3:0]));

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x %x %x %x\n",$time, cyc, crc, Result, Result2);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= {56'h0, Result, Result2}
	     ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $write("[%0t] cyc==%0d crc=%x %x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 if (sum !== 64'h4af37965592f64f9) $stop;
	 $finish;
      end
   end

endmodule

module Test (clk, Value, Result);
   input clk;
   input Value;
   output Result;

   reg Internal;

   assign Result = Internal ^ clk;

   always @(posedge clk)
     Internal <= #1 Value;
endmodule

module Test_wrap1 (clk, Value, Result);
   input clk;
   input Value;
   output Result;

   Test t (clk, Value, Result);
endmodule

module Test_wrap2 (clk, Value, Result);
   input clk;
   input Value;
   output Result;

   Test t (clk, Value, Result);
endmodule

module Testit (clk, Value, Result, Result2);
   input clk;
   input [3:0] Value;
   output [3:0] Result;
   output [3:0] Result2;

   genvar i;
   generate
      for (i = 0; i < 4; i = i + 1)
	begin : a
	   if ((i == 0) || (i == 2)) begin : gblk
	     Test_wrap1 test (clk, Value[i] , Result[i]);
	   end
	   else begin : gblk
	     Test_wrap2 test (clk, Value[i], Result[i]);
	   end
	end
   endgenerate

   assign Result2[0] = a[0].gblk.test.t.Internal;
   assign Result2[1] = a[1].gblk.test.t.Internal;
   assign Result2[2] = a[2].gblk.test.t.Internal;
   assign Result2[3] = a[3].gblk.test.t.Internal;

endmodule
