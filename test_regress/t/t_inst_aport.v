// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   // Take CRC data and apply to testblock inputs
   wire [31:0]  in = crc[31:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [15:0]          out;                    // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .out                      (out[15:0]),
              // Inputs
              .in                       (in[31:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {48'h0, out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
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

module callee (input [7:0] port [7:0], output [7:0] o);
   assign o = ^{port[0], port[1], port[2], port[3],
                port[4], port[5], port[6], port[7]};
endmodule // callee

module Test (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   in
   );

   input [31:0] in;
   output reg [15:0] out;

   wire [7:0] port [15:0];
   wire [7:0] goodport [7:0];

   always_comb begin
      port[0][7:0] = in[7:0];
      port[1][7:0] = in[16:8];
      port[2] = '0;
      port[3] = '0;
      port[4] = '0;
      port[5] = '0;
      port[6] = '0;
      port[7] = '0;
   end

   always_comb begin
      goodport[0][7:0] = in[7:0];
      goodport[1][7:0] = in[16:8];
      goodport[2] = '0;
      goodport[3] = '0;
      goodport[4] = '0;
      goodport[5] = '0;
      goodport[6] = '0;
      goodport[7] = '0;
   end

   callee good (.port(goodport), .o(out[7:0]));

   // This is a slice, unsupported by other tools, bug711
   callee bad (.port(port[7:0]), .o(out[15:8]));

endmodule
