// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc=0;
   reg [63:0]   crc;
   reg [63:0]   sum;
   reg          rst;

   // Two phases, random so nothing optimizes away, and focused so get hits
   logic        inval;
   wire [30:0]  wdat     = (cyc < 50 ? crc[30:0] : {29'h0, crc[1:0]});
   wire [30:0]  cdat     = (cyc < 50 ? crc[30:0] : {29'h0, crc[1:0]});
   wire         wdat_val = 1'b1;
   wire         camen    = crc[32];
   wire         ren      = crc[33];
   wire         wen      = crc[34];
   wire [7:0]   rwidx    = (cyc < 50 ? crc[63:56] : {6'h0, crc[57:56]});

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic                hit_d2r;                // From cam of cam.v
   logic [7:0]          hitidx_d1r;             // From cam of cam.v
   logic [255:0]        hitvec_d1r;             // From cam of cam.v
   logic [30:0]         rdat_d2r;               // From cam of cam.v
   logic                rdat_val_d2r;           // From cam of cam.v
   // End of automatics

   cam cam (/*AUTOINST*/
            // Outputs
            .hitvec_d1r                 (hitvec_d1r[255:0]),
            .hitidx_d1r                 (hitidx_d1r[7:0]),
            .hit_d2r                    (hit_d2r),
            .rdat_d2r                   (rdat_d2r[30:0]),
            .rdat_val_d2r               (rdat_val_d2r),
            // Inputs
            .clk                        (clk),
            .rst                        (rst),
            .camen                      (camen),
            .inval                      (inval),
            .cdat                       (cdat[30:0]),
            .ren                        (ren),
            .wen                        (wen),
            .wdat                       (wdat[30:0]),
            .wdat_val                   (wdat_val),
            .rwidx                      (rwidx[7:0]));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {hitvec_d1r[15:0], 15'h0, hit_d2r, rdat_val_d2r, rdat_d2r};

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
         rst <= 1'b1;
      end
      else if (cyc<10) begin
         sum <= '0;
         rst <= 1'b0;
      end
      else if (cyc==70) begin
         inval <= 1'b1;
      end
      else if (cyc==71) begin
         inval <= 1'b0;
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
`define EXPECTED_SUM 64'h5182640870b07199
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module cam
  (
   input                clk,
   input                rst,

   input                camen,
   input                inval,
   input [30:0]         cdat,
   output logic [255:0] hitvec_d1r,
   output logic [7:0]   hitidx_d1r,
   output logic         hit_d2r,

   input                ren,
   input                wen,
   input [30:0]         wdat,
   input                wdat_val,
   input [7:0]          rwidx,
   output logic [30:0]  rdat_d2r,
   output logic         rdat_val_d2r
   );

   logic                camen_d1r;
   logic                inval_d1r;
   logic                ren_d1r;
   logic                wen_d1r;
   logic [7:0]          rwidx_d1r;
   logic [30:0]         cdat_d1r;
   logic [30:0]         wdat_d1r;
   logic                wdat_val_d1r;

   always_ff @(posedge clk) begin
      camen_d1r <= camen;
      inval_d1r <= inval;
      ren_d1r <= ren;
      wen_d1r <= wen;

      cdat_d1r <= cdat;
      rwidx_d1r <= rwidx;
      wdat_d1r <= wdat;
      wdat_val_d1r <= wdat_val;
   end

   typedef struct packed {
      logic [30:0] data;
      logic        valid;
   } entry_t;
   entry_t [255:0] entries;

   always_ff @(posedge clk) begin
      if (camen_d1r) begin
         for (int i = 0; i < 256; i = i + 1) begin
            hitvec_d1r[i] <= entries[i].valid & (entries[i].data == cdat_d1r);
         end
      end
   end
   always_ff @(posedge clk) begin
      hit_d2r <= | hitvec_d1r;
   end

   always_ff @(posedge clk) begin
      if (rst) begin
         for (int i = 0; i < 256; i = i + 1) begin
            entries[i] <= '0;
         end
      end
      else if (wen_d1r) begin
         entries[rwidx_d1r] <= '{valid:wdat_val_d1r, data:wdat_d1r};
      end
      else if (inval_d1r) begin
         for (int i = 0; i < 256; i = i + 1) begin
            entries[i] <= '{valid:'0, data:entries[i].data};
         end
      end
   end

   always_ff @(posedge clk) begin
      if (ren_d1r) begin
         rdat_d2r <= entries[rwidx_d1r].data;
         rdat_val_d2r <= entries[rwidx_d1r].valid;
      end
   end

endmodule
