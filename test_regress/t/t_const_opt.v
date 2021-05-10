// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc=0;
   reg [63:0] crc;
   reg [63:0] sum;

   // Take CRC data and apply to testblock inputs
   wire [31:0] in = crc[31:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic                o;                     // From test of Test.v
   // End of automatics

   wire [31:0]          i = crc[31:0];

   Test test(/*AUTOINST*/
             // Outputs
             .o                         (o),
             // Inputs
             .clk                       (clk),
             .i                         (i[31:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {63'b0, o};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
      $display("o %b", o);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc == 0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= '0;
      end
      else if (cyc < 10) begin
         sum <= '0;
      end
      else if (cyc < 99) begin
      end
      else begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'he78be35df15ae0ab
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test(/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   clk, i
   );

   input clk;
   input [31:0] i;
   logic [31:0] d;
   logic d0, d1, d2, d3, d4, d5, d6, d7;

   output logic o;

   logic [4:0] tmp;
   assign o = ^tmp;

   always_ff @(posedge clk) begin
      d <= i;
      d0 <= i[0];
      d1 <= i[1];
      d2 <= i[2];
      d3 <= i[3];
      d4 <= i[4];
      d5 <= i[5];
      d6 <= i[6];
      d7 <= i[7];
   end
   always_ff @(posedge clk) begin
      // Cover more lines in V3Const.cpp
      tmp[0] <= (d0 || (!d0 && d1)) ^ ((!d2 && d3) || d2); // maatchOrAndNot()
      tmp[1] <= ((32'd2 ** i) & 32'h10) == 32'b0;  // replacePowShift
      tmp[2] <= ((d0 & d1) | (d0 & d2))^ ((d3 & d4) | (d5 & d4));  // replaceAndOr()
      tmp[3] <= d0 <-> d1; // replaceLogEq()
      tmp[4] <= i[0] & (i[1] & (i[2] & (i[3] | d[4])));  // ConstBitOpTreeVisitor::m_frozenNodes
   end

endmodule
