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

   // Take CRC data and apply to testblock inputs
   wire [31:0]  in = crc[31:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [63:0]		out;			// From test of Test.v
   // End of automatics

   wire			reset_l = ~(cyc<15);
   wire [63:0] 		d = crc[63:0];
   wire [8:0] 		t_wa = crc[8:0];
   wire [8:0] 		t_addr = {crc[18:17],3'b0,crc[13:10]};

   Test test (/*AUTOINST*/
	      // Outputs
	      .out			(out[63:0]),
	      // Inputs
	      .clk			(clk),
	      .reset_l			(reset_l),
	      .t_wa			(t_wa[8:0]),
	      .d			(d[63:0]),
	      .t_addr			(t_addr[8:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {out};

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
`define EXPECTED_SUM 64'h421a41d1541ea652
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk, reset_l, t_wa, d, t_addr
   );
   input	clk;
   input	reset_l;

   reg [63:0] 	m_w0 [47:0];
   reg [63:0] 	m_w1 [23:0];
   reg [63:0] 	m_w2 [23:0];
   reg [63:0] 	m_w3 [23:0];
   reg [63:0] 	m_w4 [23:0];
   reg [63:0] 	m_w5 [23:0];

   input [8:0] 	t_wa;
   input [63:0] 	d;

   always @ (posedge clk) begin
      if (~reset_l) begin : blk
	 integer i;

	 for (i=0; i<48; i=i+1) begin
	    m_w0[i] <= 64'h0;
	 end

	 for (i=0; i<24; i=i+1) begin
	    m_w1[i] <= 64'h0;
	    m_w2[i] <= 64'h0;
	    m_w3[i] <= 64'h0;
	    m_w4[i] <= 64'h0;
	    m_w5[i] <= 64'h0;
	 end
      end
      else begin
	 casez (t_wa[8:6])
	   3'd0: m_w0[t_wa[5:0]] <= d;
	   3'd1: m_w1[t_wa[4:0]] <= d;
	   3'd2: m_w2[t_wa[4:0]] <= d;
	   3'd3: m_w3[t_wa[4:0]] <= d;
	   3'd4: m_w4[t_wa[4:0]] <= d;
	   default: m_w5[t_wa[4:0]] <= d;
	 endcase
      end
   end

   input [8:0] t_addr;

   wire [63:0]	t_w0 = m_w0[t_addr[5:0]];
   wire [63:0]	t_w1 = m_w1[t_addr[4:0]];
   wire [63:0]	t_w2 = m_w2[t_addr[4:0]];
   wire [63:0]	t_w3 = m_w3[t_addr[4:0]];
   wire [63:0]	t_w4 = m_w4[t_addr[4:0]];
   wire [63:0]	t_w5 = m_w5[t_addr[4:0]];

   output reg [63:0] 	out;
   always @* begin
      casez (t_addr[8:6])
	3'd0: out = t_w0;
	3'd1: out = t_w1;
	3'd2: out = t_w2;
	3'd3: out = t_w3;
	3'd4: out = t_w4;
	default: out = t_w5;
      endcase
   end

endmodule
