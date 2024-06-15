// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Varun Koyyalagunta.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   reg [63:0] crc;
   reg [63:0] sum;

   // Take CRC data and apply to testblock inputs
   wire [31:0] in = crc[31:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [31:0]		out;			// From test of Test.v
   // End of automatics

   Test test(/*AUTOINST*/
	     // Outputs
	     .out			(out[31:0]),
	     // Inputs
	     .clk			(clk),
	     .in			(in[31:0]));

   Test2 test2(/*AUTOINST*/
	       // Inputs
	       .clk			(clk));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x sum=%x\n", $time, cyc, crc, result, sum);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      if (cyc == 0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= '0;
      end
      else if (cyc < 10) begin
         sum <= '0;
      end
      else if (cyc < 90) begin
      end
      else if (cyc == 99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h4afe43fb79d7b71e
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test(/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk, in
   );

   input clk;
   input [31:0] in;
   output reg [31:0] out;

   logic [31:0] cnt = 0;
   logic [7:0][30:0] q;
   logic cond = 0;

   always_comb begin
      for (int i = 0; i < 8; i++) begin
         if (i == (cond ? (2-cnt)%8 : 0)) begin
            q[i] = 31'(in);
         end
	 else begin
            q[i] = '0;
         end
      end
   end

   always @(posedge clk) begin
      cnt <= cnt + 1;
      cond <= ~cond;
      out <= {in[31], q[cond ? (3'd2 - cnt[2:0]) : 3'd0]};
   end

endmodule

module Test2(input wire clk);
   reg [127:1][7:0] arrayu;
   reg [6:0] index = 0;
   wire logic [7:0] selectedu = arrayu[index];
   always @(posedge clk) begin
      index <= index + 1;
      if (index == 2) $display(selectedu);
   end
endmodule
