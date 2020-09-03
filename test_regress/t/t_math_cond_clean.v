// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc=0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   // Take CRC data and apply to testblock inputs
   wire [3:0]  cnt = crc[3:0];
   wire [6:0]  decr = crc[14:8];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [3:0]           next;                   // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .next                     (next[3:0]),
              // Inputs
              .cnt                      (cnt[3:0]),
              .decr                     (decr[6:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {60'h0, next};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
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
         $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h7cd85c944415d2ef
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   next,
   // Inputs
   cnt, decr
   );

   input [3:0] cnt;
   input signed [6:0] decr;
   output reg [3:0]         next;

   always_comb begin
      reg signed [6:0] tmp;
      tmp = 0;
      // verilator lint_off WIDTH
      tmp = ($signed({1'b0, cnt}) - decr);
      // verilator lint_on WIDTH
      if ((tmp > 15)) begin
         next = 15;
      end
      else if ((tmp < 0)) begin
         next = 0;
      end
      else begin
         next = tmp[3:0];
      end
   end

endmodule
