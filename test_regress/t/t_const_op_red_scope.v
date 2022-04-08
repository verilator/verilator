// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//      $write("*-* All Finished *-*\n");
//      $finish;
// on success, or $stop.
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by ____YOUR_NAME_HERE____.
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
   wire [7:0] in = crc[7:0];

   /*AUTOWIRE*/

   wire        out0;
   wire        out1;
   wire        out2;
   wire        out3;
   wire        out4;
   wire        out5;
   wire        out6;
   wire        out7;

   /*SelFlop AUTO_TEMPLATE(.n(@),
                           .out(out@)); */

   SelFlop selflop0(/*AUTOINST*/
                    // Outputs
                    .out                (out0),                  // Templated
                    // Inputs
                    .clk                (clk),
                    .in                 (in[7:0]),
                    .n                  (0));                     // Templated
   SelFlop selflop1(/*AUTOINST*/
                    // Outputs
                    .out                (out1),                  // Templated
                    // Inputs
                    .clk                (clk),
                    .in                 (in[7:0]),
                    .n                  (1));                     // Templated
   SelFlop selflop2(/*AUTOINST*/
                    // Outputs
                    .out                (out2),                  // Templated
                    // Inputs
                    .clk                (clk),
                    .in                 (in[7:0]),
                    .n                  (2));                     // Templated
   SelFlop selflop3(/*AUTOINST*/
                    // Outputs
                    .out                (out3),                  // Templated
                    // Inputs
                    .clk                (clk),
                    .in                 (in[7:0]),
                    .n                  (3));                     // Templated

   // Aggregate outputs into a single result vector
   wire        outo = out0|out1|out2|out3;
   wire        outa = out0&out1&out2&out3;
   wire        outx = out0^out1^out2^out3;
   wire [63:0] result = {61'h0, outo, outa, outx};

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
`define EXPECTED_SUM 64'h118c5809c7856d78
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module SelFlop(/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk, in, n
   );

   input clk;
   input [7:0] in;
   input [2:0]  n;
   output reg out;

   // verilator no_inline_module

   always @(posedge clk) begin
      out <= in[n];
   end
endmodule
