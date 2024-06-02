// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
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
   wire [4:0] cnt_i = (crc[4:0] <= 5'd17) ? crc[4:0] : 5'd0;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [63:0]         out_o;                  // From test of Test.v
   // End of automatics

   Test test(/*AUTOINST*/
             // Outputs
             .out_o                     (out_o[63:0]),
             // Inputs
             .cnt_i                     (cnt_i[4:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = out_o;

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
`define EXPECTED_SUM 64'h1f324087bbba0bfa
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test
  (input logic [4:0]   cnt_i,
   output logic [63:0] out_o);

   logic [17:0][63:0]  data;
   initial begin
      for (int a = 0; a < 18; ++a)
        data[a] = {8{a[7:0]}};
   end

   // verilator lint_off WIDTH
   assign out_o = data[5'd17 - cnt_i];

endmodule
