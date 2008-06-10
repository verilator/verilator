// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;
   reg 		rst_n;

   // Take CRC data and apply to testblock inputs

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [2:0]		pos;			// From test of Test.v
   // End of automatics

   Test test (
	      // Outputs
	      .pos			(pos[2:0]),
	      /*AUTOINST*/
	      // Inputs
	      .clk			(clk),
	      .rst_n			(rst_n));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {61'h0, pos};

   // What checksum will we end up with
`define EXPECTED_SUM 64'h039ea4d039c2e70b

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      rst_n <= ~1'b0;
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
	 rst_n <= ~1'b1;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
	 rst_n <= ~1'b1;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test
  #(parameter SAMPLE_WIDTH = 5 )
   (
`ifdef verilator  // UNSUPPORTED
    output reg [$clog2(SAMPLE_WIDTH-1)-1:0]         pos,
`else
    output reg [log2(SAMPLE_WIDTH-1)-1:0]         pos,
`endif
    // System
    input 	clk,
    input 	rst_n
    );

   function integer log2(input integer arg);
      begin
	 for(log2=0; arg>0; log2=log2+1)
	   arg = (arg >> 1);
      end
   endfunction

   always @ (posedge clk or negedge  rst_n)
     if (!rst_n) begin
	pos   <= 0;
     end
     else begin
	pos <= pos + 1;
     end
endmodule
