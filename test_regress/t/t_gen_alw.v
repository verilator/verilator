// DESCRIPTION: Verilator: Verilog Test module

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [9:0]  in = crc[9:0];

   /*AUTOWIRE*/

   Test test (/*AUTOINST*/
	      // Inputs
	      .clk			(clk),
	      .in			(in[9:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {64'h0};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
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
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h0
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Inputs
   clk, in
   );
   input clk;
   input [9:0] in;

   reg a [9:0];
   integer ai;
   always @* begin
      for (ai=0;ai<10;ai=ai+1) begin
	 a[ai]=in[ai];
      end
   end

   reg [1:0] b [9:0];
   integer   j;

   generate
      genvar i;
      for (i=0; i<2; i=i+1) begin
	 always @(posedge clk) begin
	    for (j=0; j<10; j=j+1) begin
	       if (a[j])
		 b[i][j] <= 1'b0;
	       else
		 b[i][j] <= 1'b1;
	    end
	 end
      end
   endgenerate
endmodule
