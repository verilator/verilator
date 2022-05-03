// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [255:0]  sum;

   // Take CRC data and apply to testblock inputs
   wire [127:0]  in = {~crc[63:0], crc[63:0]};

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [127:0]         o1;                     // From test of Test.v
   wire [127:0]         o2;                     // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .o1                       (o1[127:0]),
              .o2                       (o2[127:0]),
              // Inputs
              .in                       (in[127:0]));

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x %x\n", $time, cyc, crc, o1, o2);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= {o1,o2} ^ {sum[254:0],sum[255]^sum[2]^sum[0]};
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
`define EXPECTED_SUM 256'h008a080aaa000000140550404115dc7b008a080aaae7c8cd897bc1ca49c9350a
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   o1, o2,
   // Inputs
   in
   );

   input [127:0] in;
   output logic [127:0] o1;
   output logic [127:0] o2;

   always_comb begin: b_test
      logic [127:0] tmpp;
      logic [127:0] tmp;
      tmp  = '0;
      tmpp = '0;

      tmp[63:0]  = in[63:0];
      tmpp[63:0] = in[63:0];

      tmpp[63:0] = {tmp[0+:32], tmp[32+:32]};
      tmp[63:0]  = {tmp[0+:32], tmp[32+:32]};

      o1 = tmp;
      o2 = tmpp;
   end

endmodule
