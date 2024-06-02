// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Varun Koyyalagunta.
// SPDX-License-Identifier: CC0-1.0

// bug1015
module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   // Take CRC data and apply to testblock inputs
   wire  [1:0] i = crc[1:0];
   logic [1:0] o [13:10] ;

   Test test (/*AUTOINST*/
              // Outputs
              .o                        (o/*[1:0].[3:0]*/),
              // Inputs
              .i                        (i[1:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {32'h0, 6'h0,o[13], 6'h0,o[12], 6'h0,o[11], 6'h0,o[10]};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x sum=%x\n", $time, cyc, crc, result, sum);
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
`define EXPECTED_SUM 64'hb42b2f48a0a9375a
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test
  (
   output logic [1:0] o [3:0],
   //but this works
   //logic [N-1:0] o
   input        [1:0] i);

   parameter N = 4;

   logic [1:0]        a [3:0]; initial a = '{2'h0,2'h1,2'h2,2'h3};

   sub sub [N-1:0] (.o  (o),  // many-to-many
                    .a  (a),  // many-to-many
                    .i  (i)); // many-to-one
endmodule

module sub
  (
   input  logic [1:0] i,
   input  logic [1:0] a,
   output logic [1:0] o
   );
   assign o = i + a;
endmodule
