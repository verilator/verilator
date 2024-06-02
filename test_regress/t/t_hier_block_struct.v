// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Varun Koyyalagunta.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
    logic x;
} nested_named_t;

typedef struct packed {
    struct packed {
        logic x;
    } nested_anonymous;
    nested_named_t nested_named;
    logic [1:0] x;
} nibble_t;

module t(
   clk
   );
   input clk;

   integer cyc = 0;
   logic [63:0] crc;
   logic [63:0] sum;

   // Take CRC data and apply to testblock inputs
   nibble_t[7:0] in;
   assign in = crc[31:0];

   nibble_t[7:0] out;

   Test test(
             .out0                      ({out[1], out[0]}),
             .out1                      ({{out[5], out[4]}, {out[3], out[2]}}),
             .out2                      (out[6]),
             .out3                      (out[7]),
             .clk                       (clk),
             .in0                       (in[0]),
             .in1                       (in[1]),
             .in2                       ({in[5], in[4], in[3], in[2]}),
             .in3                       ({in[7], in[6]}));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
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

module Test(
   // Outputs
   output nibble_t [1:0] out0,
   output nibble_t [1:0] out1[2],
   output nibble_t       out2,
   output nibble_t       out3,
   // Inputs
   input clk,
   input nibble_t       in0,
   input nibble_t       in1,
   input nibble_t [3:0] in2,
   input nibble_t       in3[2]
   ); /*verilator hier_block*/


   always @(posedge clk) begin
      {out3, out2, out1[0], out1[1], out0} <= {in3[0], in3[1], in2, in1, in0};
   end

endmodule
