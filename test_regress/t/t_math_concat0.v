// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
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
   wire [15:0]  in = crc[15:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [15:0]          outa;                   // From test of Test.v
   wire [15:0]          outb;                   // From test of Test.v
   wire [15:0]          outc;                   // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .outa                     (outa[15:0]),
              .outb                     (outb[15:0]),
              .outc                     (outc[15:0]),
              // Inputs
              .clk                      (clk),
              .in                       (in[15:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {16'h0, outa, outb, outc};

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
`define EXPECTED_SUM 64'h09be74b1b0f8c35d
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   outa, outb, outc,
   // Inputs
   clk, in
   );

   input clk;
   input [15:0]      in;
   output reg [15:0] outa;
   output reg [15:0] outb;
   output reg [15:0] outc;

   parameter WIDTH = 0;
   always @(posedge clk) begin
      outa <= {in};
      outb <= {{WIDTH{1'b0}}, in};
      outc <= {in, {WIDTH{1'b0}}};
   end
endmodule
