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
   wire [3:0]   in = crc[3:0];
   wire         clken = crc[4];
   wire         rstn = !(cyc < 20 || (crc[11:8]==0));

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [3:0]           ff_out;                 // From test of Test.v
   wire [3:0]           fg_out;                 // From test of Test.v
   wire [3:0]           fh_out;                 // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .ff_out                   (ff_out[3:0]),
              .fg_out                   (fg_out[3:0]),
              .fh_out                   (fh_out[3:0]),
              // Inputs
              .clk                      (clk),
              .clken                    (clken),
              .rstn                     (rstn),
              .in                       (in[3:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {52'h0, ff_out, fg_out, fh_out};

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
`define EXPECTED_SUM 64'h77979747fd1b3a5a
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule


module Test
  (/*AUTOARG*/
   // Outputs
   ff_out, fg_out, fh_out,
   // Inputs
   clk, clken, rstn, in
   );

   input clk;
   input clken;
   input rstn;

   input [3:0] in;

   output reg [3:0] ff_out;
   reg [3:0] ff_10;
   reg [3:0] ff_11;
   reg [3:0] ff_12;
   reg [3:0] ff_13;
   always @(posedge clk) begin
      if ((rstn == 0)) begin
         ff_10 <= 0;
         ff_11 <= 0;
         ff_12 <= 0;
         ff_13 <= 0;
      end
      else begin
         ff_10 <= in;
         ff_11 <= ff_10;
         ff_12 <= ff_11;
         ff_13 <= ff_12;
         ff_out <= ff_13;
      end
   end

   output reg [3:0] fg_out;
   reg [3:0] fg_10;
   reg [3:0] fg_11;
   reg [3:0] fg_12;
   reg [3:0] fg_13;
   always @(posedge clk) begin
      if (clken) begin
         if ((rstn == 0)) begin
            fg_10 <= 0;
            fg_11 <= 0;
            fg_12 <= 0;
            fg_13 <= 0;
         end
         else begin
            fg_10 <= in;
            fg_11 <= fg_10;
            fg_12 <= fg_11;
            fg_13 <= fg_12;
            fg_out <= fg_13;
         end
      end
   end

   output reg [3:0] fh_out;
   reg [3:0] fh_10;
   reg [3:0] fh_11;
   reg [3:0] fh_12;
   reg [3:0] fh_13;
   always @(posedge clk) begin
      if ((rstn == 0)) begin
         fh_10 <= 0;
         fh_11 <= 0;
         fh_12 <= 0;
         fh_13 <= 0;
      end
      else begin
         if (clken) begin
            fh_10 <= in;
            fh_11 <= fh_10;
            fh_12 <= fh_11;
            fh_13[3:1] <= fh_12[3:1];
            fh_13[0] <= fh_12[0];
            fh_out <= fh_13;
         end
      end
   end


endmodule
