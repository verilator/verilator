// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

import "DPI-C" context function int import_func0();
import "DPI-C" context function int import_func1();
import "DPI-C" context function int import_func2();
import "DPI-C" context function int import_func3();
import "DPI-C" context function int import_func4();

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

   wire [31:0] i = crc[31:0];
   wire out;

   Test test(
             // Outputs
             .out                       (out),
             // Inputs
             .clk                       (clk),
             .i                         (i[31:0]));

   wire [63:0] result = {63'b0, out};

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
         if (import_func1() != 1) $stop;  // this must be the first call
         if (import_func3() != 1) $stop;  // this must be the first call
         if (import_func4() < 95) $stop;  // expected to return around 100
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h162c58b1635b8d6e
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
   clk, i
   );

   input clk;
   input [31:0] i;

   output wire out;

   logic [2:0] tmp;
   assign out = ^tmp;

   always_ff @(posedge clk) begin
      // Note that import_func?() always returns positive integer,
      // so '|(import_func?())' is always 1'b1
      tmp[0] <= |(import_func0()) || |(import_func1()); // import_fnc1 must not be called
      tmp[1] <= !(|(import_func2())) && |(import_func3()); // import_fnc3 must not be called
      tmp[2] <= ^(0 * import_func4());  // import_func1 has side effect, so must be executed anyway.
   end

endmodule
