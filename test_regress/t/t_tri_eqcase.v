// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   wire [3:0]  drv_a = crc[3:0];
   wire [3:0]  drv_b = crc[7:4];
   wire [3:0]  drv_e = crc[19:16];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [8:0]           match1;                 // From test1 of Test1.v
   wire [8:0]           match2;                 // From test2 of Test2.v
   // End of automatics

   Test1 test1 (/*AUTOINST*/
                // Outputs
                .match1                 (match1[8:0]),
                // Inputs
                .drv_a                  (drv_a[3:0]),
                .drv_e                  (drv_e[3:0]));
   Test2 test2 (/*AUTOINST*/
                // Outputs
                .match2                 (match2[8:0]),
                // Inputs
                .drv_a                  (drv_a[3:0]),
                .drv_e                  (drv_e[3:0]));

   // Aggregate outputs into a single result vector
   wire [63:0]          result = {39'h0, match2, 7'h0, match1};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x m1=%x m2=%x  (%b??%b:%b)\n", $time, cyc, crc, match1, match2, drv_e,drv_a,drv_b);
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
`define EXPECTED_SUM 64'hc0c4a2b9aea7c4b4
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test1
  (
   input wire [3:0] drv_a,
   input wire [3:0] drv_e,
   output wire [8:0] match1
   );

   wire [2:1]       drv_all;
   bufif1 bufa [2:1] (drv_all, drv_a[2:1], drv_e[2:1]);

`ifdef VERILATOR
   // At present Verilator only allows comparisons with Zs
   assign match1[0] = (drv_a[2:1]== 2'b00 && drv_e[2:1]==2'b11);
   assign match1[1] = (drv_a[2:1]== 2'b01 && drv_e[2:1]==2'b11);
   assign match1[2] = (drv_a[2:1]== 2'b10 && drv_e[2:1]==2'b11);
   assign match1[3] = (drv_a[2:1]== 2'b11 && drv_e[2:1]==2'b11);
`else
   assign match1[0] = drv_all === 2'b00;
   assign match1[1] = drv_all === 2'b01;
   assign match1[2] = drv_all === 2'b10;
   assign match1[3] = drv_all === 2'b11;
`endif
   assign match1[4] = drv_all === 2'bz0;
   assign match1[5] = drv_all === 2'bz1;
   assign match1[6] = drv_all === 2'bzz;
   assign match1[7] = drv_all === 2'b0z;
   assign match1[8] = drv_all === 2'b1z;
endmodule

module Test2
  (
   input wire [3:0] drv_a,
   input wire [3:0] drv_e,
   output wire [8:0] match2
   );

   wire [2:1]       drv_all;
   bufif1 bufa [2:1] (drv_all, drv_a[2:1], drv_e[2:1]);

`ifdef VERILATOR
   assign match2[0] = (drv_all !== 2'b00 || drv_e[2:1]!=2'b11);
   assign match2[1] = (drv_all !== 2'b01 || drv_e[2:1]!=2'b11);
   assign match2[2] = (drv_all !== 2'b10 || drv_e[2:1]!=2'b11);
   assign match2[3] = (drv_all !== 2'b11 || drv_e[2:1]!=2'b11);
`else
   assign match2[0] = drv_all !== 2'b00;
   assign match2[1] = drv_all !== 2'b01;
   assign match2[2] = drv_all !== 2'b10;
   assign match2[3] = drv_all !== 2'b11;
`endif
   assign match2[4] = drv_all !== 2'bz0;
   assign match2[5] = drv_all !== 2'bz1;
   assign match2[6] = drv_all !== 2'bzz;
   assign match2[7] = drv_all !== 2'b0z;
   assign match2[8] = drv_all !== 2'b1z;
endmodule
