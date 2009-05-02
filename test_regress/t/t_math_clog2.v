// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

`ifdef verilator
 `define CLOG2 $clog2
`else
 `define CLOG2 clog2_emulate
`endif

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Need temp wires as function has different width rules than $clog2
   wire [127:0] pows = 128'h1<<crc[7:0];
   wire [127:0] npows = ~pows;

   wire [31:0] 	out  = `CLOG2(crc[7:0]);
   wire [31:0] 	out2 = `CLOG2(crc);
   wire [31:0] 	out3 = `CLOG2(pows);
   wire [31:0] 	out4 = `CLOG2(npows);

   // Aggregate outputs into a single result vector
   wire [63:0] result = {out4[15:0], out3[15:0], out2[15:0], out[15:0]};

`define EXPECTED_SUM 64'h73c48afee4f0cb57

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 crc <= 64'h0;
	 if (`CLOG2(32'h0) != 0) $stop;
	 if (`CLOG2(32'h1) != 0) $stop;
	 if (`CLOG2(32'h4) != 2) $stop;
	 if (`CLOG2(32'h7) != 3) $stop;
	 if (`CLOG2(32'h8) != 3) $stop;
	 if (`CLOG2(32'h9) != 4) $stop;
	 if (`CLOG2({32{1'b1}}) != 32) $stop;
	 if (`CLOG2({1'b1,32'b0}) != 32) $stop;
	 if (`CLOG2({64{1'b1}}) != 64) $stop;
	 if (`CLOG2({1'b1,64'b0}) != 64) $stop;
	 if (`CLOG2({128{1'b1}}) != 128) $stop;
	 if (`CLOG2({1'b1,128'b0}) != 128) $stop;
	 if (`CLOG2({2'b10,128'b0}) != 129) $stop;
      end
      else if (cyc==1) begin
	 crc <= 64'h1;
	 if (result[31:0] != {16'd0, 16'd0}) $stop;
      end
      else if (cyc==2) begin
	 crc <= 64'h3;
	 if (result[31:0] != {16'd0, 16'd0}) $stop;
      end
      else if (cyc==3) begin
	 crc <= {64{1'b1}};
	 if (result[31:0] != {16'd2, 16'd2}) $stop;
      end
      else if (cyc==4) begin
	 if (result[31:0] != {16'd64, 16'd8}) $stop;
      end
      else if (cyc==8) begin
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hcbc77bb9b3784ea0) $stop;
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

   function integer clog2_emulate(input [130:0] arg);
      begin
	 if (arg!=0) arg = arg - 1;
	 for (clog2_emulate=0; arg!=0; clog2_emulate=clog2_emulate+1)
	   arg = (arg >> 1);
      end
   endfunction
endmodule
