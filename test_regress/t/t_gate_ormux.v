// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   logic [31:0] rdata;
   logic [31:0] rdata2;
   wire [31:0]  wdata = crc[31:0];
   wire [15:0]  sel = {11'h0, crc[36:32]};
   wire         we = crc[48];

   Test test (/*AUTOINST*/
              // Outputs
              .rdata                    (rdata[31:0]),
              .rdata2                   (rdata2[31:0]),
              // Inputs
              .clk                      (clk),
              .we                       (we),
              .sel                      (sel[15:0]),
              .wdata                    (wdata[31:0]));

   // 5.07 4.42 -> 13%
   wire [63:0] result = {rdata2, rdata};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      if (rdata2 != rdata) $stop;
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= '0;
      end
      else if (cyc<10) begin
         sum <= '0;
      end
      else if (cyc == 99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
`define EXPECTED_SUM 64'h8977713eb467bc86
         if (sum !== `EXPECTED_SUM) $stop;
      end
      else if (cyc == `SIM_CYCLES) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test(/*AUTOARG*/
   // Outputs
   rdata, rdata2,
   // Inputs
   clk, we, sel, wdata
   );
   input clk;
   input we;
   input [15:0] sel;
   input [31:0] wdata;
   output logic [31:0] rdata;
   output logic [31:0] rdata2;

   logic               we_d1r;
   logic [15:0]        sel_d1r;
   logic [31:0]        wdata_d1r;
   always_ff @ (posedge clk) begin
      we_d1r <= we;
      sel_d1r <= sel;
      wdata_d1r <= wdata;
   end

   reg [31:0] csr0000;
   reg [31:0] csr0001;
   reg [31:0] csr0002;
   reg [31:0] csr0003;
   reg [31:0] csr0004;
   reg [31:0] csr0005;
   reg [31:0] csr0006;
   reg [31:0] csr0007;
   reg [31:0] csr0008;
   reg [31:0] csr0009;
   reg [31:0] csr000a;
   reg [31:0] csr000b;
   reg [31:0] csr000c;
   reg [31:0] csr000d;
   reg [31:0] csr000e;
   reg [31:0] csr000f;
   wire [31:0] csr0010 = 32'h33675230;
   wire [31:0] csr0011 = 32'h00fa2144;
   wire [31:0] csr0012 = 32'h6a5e8e10;
   wire [31:0] csr0013 = 32'h000a5b5e;
   wire [31:0] csr0014 = 32'h002fe51b;
   wire [31:0] csr0015 = 32'h00027e00;
   wire [31:0] csr0016 = 32'h0000e3c0;
   wire [31:0] csr0017 = 32'h00efcf16;
   wire [31:0] csr0018 = 32'h007a2600;
   wire [31:0] csr0019 = 32'h0a4a9f10;
   wire [31:0] csr001a = 32'h7d789de3;
   wire [31:0] csr001b = 32'h40f655f9;
   wire [31:0] csr001c = 32'hadad01f4;
   wire [31:0] csr001d = 32'h02e7b33c;
   wire [31:0] csr001e = 32'h12101533;
   wire [31:0] csr001f = 32'h2cc1cce5;
   initial begin
      csr0000 = 32'he172d365;
      csr0001 = 32'h35cc25e2;
      csr0002 = 32'haf48436e;
      csr0003 = 32'h135e55e4;
      csr0004 = 32'h5fd6e48a;
      csr0005 = 32'hb07d34ad;
      csr0006 = 32'h2aa05deb;
      csr0007 = 32'hfe97b680;
      csr0008 = 32'h960f20bb;
      csr0009 = 32'h251129f0;
      csr000a = 32'hef3d2f93;
      csr000b = 32'hef4bc127;
      csr000c = 32'h3dfecb10;
      csr000d = 32'h1b4690f5;
      csr000e = 32'ha07822ab;
      csr000f = 32'hf817cbf6;
   end

   always_ff @ (posedge clk) begin
      if (we_d1r && sel_d1r == 16'h0000) csr0000 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h0001) csr0001 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h0002) csr0002 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h0003) csr0003 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h0004) csr0004 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h0005) csr0005 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h0006) csr0006 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h0007) csr0007 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h0008) csr0008 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h0009) csr0009 <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h000a) csr000a <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h000b) csr000b <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h000c) csr000c <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h000d) csr000d <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h000e) csr000e <= wdata_d1r;
      if (we_d1r && sel_d1r == 16'h000f) csr000f <= wdata_d1r;
   end

   wire dec0000 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] && !sel_d1r[3] && !sel_d1r[2] && !sel_d1r[1] && !sel_d1r[0];
   wire dec0001 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] && !sel_d1r[3] && !sel_d1r[2] && !sel_d1r[1] &&  sel_d1r[0];
   wire dec0002 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] && !sel_d1r[3] && !sel_d1r[2] &&  sel_d1r[1] && !sel_d1r[0];
   wire dec0003 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] && !sel_d1r[3] && !sel_d1r[2] &&  sel_d1r[1] &&  sel_d1r[0];
   wire dec0004 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] && !sel_d1r[3] &&  sel_d1r[2] && !sel_d1r[1] && !sel_d1r[0];
   wire dec0005 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] && !sel_d1r[3] &&  sel_d1r[2] && !sel_d1r[1] &&  sel_d1r[0];
   wire dec0006 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] && !sel_d1r[3] &&  sel_d1r[2] &&  sel_d1r[1] && !sel_d1r[0];
   wire dec0007 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] && !sel_d1r[3] &&  sel_d1r[2] &&  sel_d1r[1] &&  sel_d1r[0];
   wire dec0008 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] &&  sel_d1r[3] && !sel_d1r[2] && !sel_d1r[1] && !sel_d1r[0];
   wire dec0009 = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] &&  sel_d1r[3] && !sel_d1r[2] && !sel_d1r[1] &&  sel_d1r[0];
   wire dec000a = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] &&  sel_d1r[3] && !sel_d1r[2] &&  sel_d1r[1] && !sel_d1r[0];
   wire dec000b = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] &&  sel_d1r[3] && !sel_d1r[2] &&  sel_d1r[1] &&  sel_d1r[0];
   wire dec000c = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] &&  sel_d1r[3] &&  sel_d1r[2] && !sel_d1r[1] && !sel_d1r[0];
   wire dec000d = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] &&  sel_d1r[3] &&  sel_d1r[2] && !sel_d1r[1] &&  sel_d1r[0];
   wire dec000e = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] &&  sel_d1r[3] &&  sel_d1r[2] &&  sel_d1r[1] && !sel_d1r[0];
   wire dec000f = sel_d1r[15:6] == 0 && !sel_d1r[5] && !sel_d1r[4] &&  sel_d1r[3] &&  sel_d1r[2] &&  sel_d1r[1] &&  sel_d1r[0];
   wire dec0010 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] && !sel_d1r[3] && !sel_d1r[2] && !sel_d1r[1] && !sel_d1r[0];
   wire dec0011 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] && !sel_d1r[3] && !sel_d1r[2] && !sel_d1r[1] &&  sel_d1r[0];
   wire dec0012 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] && !sel_d1r[3] && !sel_d1r[2] &&  sel_d1r[1] && !sel_d1r[0];
   wire dec0013 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] && !sel_d1r[3] && !sel_d1r[2] &&  sel_d1r[1] &&  sel_d1r[0];
   wire dec0014 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] && !sel_d1r[3] &&  sel_d1r[2] && !sel_d1r[1] && !sel_d1r[0];
   wire dec0015 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] && !sel_d1r[3] &&  sel_d1r[2] && !sel_d1r[1] &&  sel_d1r[0];
   wire dec0016 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] && !sel_d1r[3] &&  sel_d1r[2] &&  sel_d1r[1] && !sel_d1r[0];
   wire dec0017 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] && !sel_d1r[3] &&  sel_d1r[2] &&  sel_d1r[1] &&  sel_d1r[0];
   wire dec0018 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] &&  sel_d1r[3] && !sel_d1r[2] && !sel_d1r[1] && !sel_d1r[0];
   wire dec0019 = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] &&  sel_d1r[3] && !sel_d1r[2] && !sel_d1r[1] &&  sel_d1r[0];
   wire dec001a = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] &&  sel_d1r[3] && !sel_d1r[2] &&  sel_d1r[1] && !sel_d1r[0];
   wire dec001b = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] &&  sel_d1r[3] && !sel_d1r[2] &&  sel_d1r[1] &&  sel_d1r[0];
   wire dec001c = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] &&  sel_d1r[3] &&  sel_d1r[2] && !sel_d1r[1] && !sel_d1r[0];
   wire dec001d = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] &&  sel_d1r[3] &&  sel_d1r[2] && !sel_d1r[1] &&  sel_d1r[0];
   wire dec001e = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] &&  sel_d1r[3] &&  sel_d1r[2] &&  sel_d1r[1] && !sel_d1r[0];
   wire dec001f = sel_d1r[15:6] == 0 && !sel_d1r[5] &&  sel_d1r[4] &&  sel_d1r[3] &&  sel_d1r[2] &&  sel_d1r[1] &&  sel_d1r[0];

   assign rdata = (32'h0
                   | {32{dec0000}} & csr0000
                   | {32{dec0001}} & csr0001
                   | {32{dec0002}} & csr0002
                   | {32{dec0003}} & csr0003
                   | {32{dec0004}} & csr0004
                   | {32{dec0005}} & csr0005
                   | {32{dec0006}} & csr0006
                   | {32{dec0007}} & csr0007
                   | {32{dec0008}} & csr0008
                   | {32{dec0009}} & csr0009
                   | {32{dec000a}} & csr000a
                   | {32{dec000b}} & csr000b
                   | {32{dec000c}} & csr000c
                   | {32{dec000d}} & csr000d
                   | {32{dec000e}} & csr000e
                   | {32{dec000f}} & csr000f
                   | {32{dec0010}} & csr0010
                   | {32{dec0011}} & csr0011
                   | {32{dec0012}} & csr0012
                   | {32{dec0013}} & csr0013
                   | {32{dec0014}} & csr0014
                   | {32{dec0015}} & csr0015
                   | {32{dec0016}} & csr0016
                   | {32{dec0017}} & csr0017
                   | {32{dec0018}} & csr0018
                   | {32{dec0019}} & csr0019
                   | {32{dec001a}} & csr001a
                   | {32{dec001b}} & csr001b
                   | {32{dec001c}} & csr001c
                   | {32{dec001d}} & csr001d
                   | {32{dec001e}} & csr001e
                   | {32{dec001f}} & csr001f
                  );

   always_comb begin
      case (sel_d1r)
        16'h0000: rdata2 = csr0000;
        16'h0001: rdata2 = csr0001;
        16'h0002: rdata2 = csr0002;
        16'h0003: rdata2 = csr0003;
        16'h0004: rdata2 = csr0004;
        16'h0005: rdata2 = csr0005;
        16'h0006: rdata2 = csr0006;
        16'h0007: rdata2 = csr0007;
        16'h0008: rdata2 = csr0008;
        16'h0009: rdata2 = csr0009;
        16'h000a: rdata2 = csr000a;
        16'h000b: rdata2 = csr000b;
        16'h000c: rdata2 = csr000c;
        16'h000d: rdata2 = csr000d;
        16'h000e: rdata2 = csr000e;
        16'h000f: rdata2 = csr000f;
        16'h0010: rdata2 = csr0010;
        16'h0011: rdata2 = csr0011;
        16'h0012: rdata2 = csr0012;
        16'h0013: rdata2 = csr0013;
        16'h0014: rdata2 = csr0014;
        16'h0015: rdata2 = csr0015;
        16'h0016: rdata2 = csr0016;
        16'h0017: rdata2 = csr0017;
        16'h0018: rdata2 = csr0018;
        16'h0019: rdata2 = csr0019;
        16'h001a: rdata2 = csr001a;
        16'h001b: rdata2 = csr001b;
        16'h001c: rdata2 = csr001c;
        16'h001d: rdata2 = csr001d;
        16'h001e: rdata2 = csr001e;
        16'h001f: rdata2 = csr001f;
        default: rdata2 = 0;
      endcase
   end

endmodule
