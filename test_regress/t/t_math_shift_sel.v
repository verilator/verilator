// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
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
   wire [106:0]  in = {~crc[42:0], crc[63:0]};

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]           out1;                   // From test of Test.v
   wire [7:0]           out2;                   // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .out1                     (out1[7:0]),
              .out2                     (out2[7:0]),
              // Inputs
              .in                       (in[106:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {48'h0, out1, out1};

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
         sum <= '0;
      end
      else if (cyc<10) begin
         sum <= '0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'hc746017202a24ecc
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   out1, out2,
   // Inputs
   in
   );

   // Replace this module with the device under test.
   //
   // Change the code in the t module to apply values to the inputs and
   // merge the output values into the result vector.

   input [106:0]    in;
   output [7:0]     out1, out2;

   // verilator lint_off WIDTH
   // Better written as onibble[99 +: 8]. Verilator will convert it.
   wire [7:0]       out1 = (in >>> 99) & 255;
   // verilator lint_on WIDTH
   wire [7:0]       out2 = in[106:99];

endmodule
