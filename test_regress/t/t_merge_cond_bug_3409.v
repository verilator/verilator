// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Raynard Qiao.
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
   wire [3:0] din = crc[3:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire                 row_found;              // From test of Test.v
   wire [1:0]           row_idx;                // From test of Test.v
   // End of automatics

   Test test(/*AUTOINST*/
             // Outputs
             .row_idx                   (row_idx[1:0]),
             .row_found                 (row_found),
             // Inputs
             .din                       (din));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {48'b0, din, 7'b0, row_found, 2'b0, row_idx};

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
      else if (cyc == 99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h8b61595b704e511f
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test(/*AUTOARG*/
   // Outputs
   row_idx, row_found,
   // Inputs
   din
   );

   input din;
   output [1:0] row_idx;
   output       row_found;

   reg [3:0]    din;
   reg [3:0]    wide_din;
   reg          row_found;
   reg [1:0]    row_idx;

   always_comb begin
      integer x;
      row_idx = {2{1'b0}};
      row_found = 1'b0;
      // Bug #3409: After unrolling, these conditionals should not be merged
      // as row_found is assigned.
      for (x = 0; $unsigned(x) < 4; x = x + 1) begin
         row_idx = !row_found ? x[1:0] : row_idx;
         row_found = !row_found ? din[x] : row_found;
      end
   end

endmodule
