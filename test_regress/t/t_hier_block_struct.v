// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Varun Koyyalagunta.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
    logic [31:0] crc;
} crc_t;

module t(
   clk
   );
   input clk;

   integer cyc = 0;
   logic [63:0] crc;
   logic [63:0] sum;

   // Take CRC data and apply to testblock inputs
   crc_t in;
   assign in = crc[31:0];

   crc_t          out;

   Test test(
             .out                       (out),
             .clk                       (clk),
             .in                        (in));

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
   output crc_t out,
   // Inputs
   input clk,
   input crc_t in
   ); /*verilator hier_block*/


   always @(posedge clk) begin
      out <= in;
   end

endmodule
