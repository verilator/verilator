// DESCRIPTION: Verilator: Verilog Test module
//
// Exercises the priority-encoder / leading-one ("bit-width", find-last-set) loop
// idiom that V3Unroll lowers to $mostsetbitp1 (CLZ).
//
//   Positive cases (MUST lower):   canonical for(b=0;b<W;b++) if(v[b]) n=b+1
//     covering the I (<=32b), Q (33-64b) and W (>64b) runtime paths.
//   Negative cases (MUST NOT lower): non-canonical scans whose result differs
//     from $mostsetbitp1(vec).  These both (a) self-check their own values and
//     (b) are counted by the .py via --stats so a wrong lowering is caught.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  // ---- positive: should lower (I / Q / W paths) ----
  logic [31:0] p32;  logic [5:0] n32;
  logic [47:0] p48;  logic [6:0] n48;
  logic [79:0] p80;  logic [6:0] n80;
  logic [31:0] pc;   logic [5:0] nc;   // population count (count-ones) -> $countones
  logic [31:0] pu;   logic [5:0] nu;   // unsigned loop var (still $mostsetbitp1)
  always_comb begin n32 = 0; for (int b = 0; b < 32; b++) if (p32[b]) n32 = 6'(b + 1); end
  always_comb begin n48 = 0; for (int b = 0; b < 48; b++) if (p48[b]) n48 = 7'(b + 1); end
  always_comb begin n80 = 0; for (int b = 0; b < 80; b++) if (p80[b]) n80 = 7'(b + 1); end
  always_comb begin nc  = 0; for (int b = 0; b < 32; b++) if (pc[b])  nc  = nc + 1;   end
  always_comb begin nu  = 0; for (int unsigned b = 0; b < 32; b++) if (pu[b]) nu = 6'(b + 1); end

  // ---- negative: must NOT lower (each scans a subset / computes a different value) ----
  logic [31:0] vn;
  logic [5:0] e_step2;   // step 2 (even bits only)
  logic [6:0] e_start1;  // starts at 1 (skips bit 0)
  logic [6:0] e_mul;     // target = idx*2 + 1
  logic [5:0] e_off;     // selects vec[idx+1]
  logic [5:0] e_noP1;    // target = idx (no +1)
  logic [31:0] vw;       // separate vec with a set bit above the scan bound
  logic [5:0] e_narrow;  // bound W=16 != width(vec)=32 (scans only a prefix)
  always_comb begin e_step2  = 0; for (int b = 0; b < 32; b += 2) if (vn[b])     e_step2  = 6'(b + 1); end
  always_comb begin e_start1 = 0; for (int b = 1; b < 32; b++)    if (vn[b])     e_start1 = 7'(b + 1); end
  always_comb begin e_mul    = 0; for (int b = 0; b < 32; b++)    if (vn[b])     e_mul    = 7'(2 * b + 1); end
  always_comb begin e_off    = 0; for (int b = 0; b < 31; b++)    if (vn[b + 1]) e_off    = 6'(b + 1); end
  always_comb begin e_noP1   = 0; for (int b = 0; b < 32; b++)    if (vn[b])     e_noP1   = 6'(b); end
  always_comb begin e_narrow = 0; for (int b = 0; b < 16; b++)    if (vw[b])     e_narrow = 6'(b + 1); end

  integer cyc = 0;
  integer fails = 0;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      p32 <= 32'h8000_0000;                 // MSB  -> 32
      p48 <= 48'h0; p48[47] <= 1'b1;        // MSB  -> 48 (Q path)
      p80 <= 80'h0; p80[79] <= 1'b1;        // MSB  -> 80 (W path)
      pc  <= 32'hf0f0_f0f0;                 // 16 set bits
      pu  <= 32'h0001_0000;                 // bit 16 -> 17
      vn  <= 32'h0000_00b4;                 // bits {2,4,5,7} set
      vw  <= 32'h0010_0008;                 // bits {3,20}: prefix-scan(16)->4, full->21
    end
    else if (cyc == 1) begin
      if (n32 !== 6'd32) fails = fails + 1;
      if (n48 !== 7'd48) fails = fails + 1;
      if (n80 !== 7'd80) fails = fails + 1;
      if (nc  !== 6'd16) fails = fails + 1;  // popcount(0xF0F0F0F0)
      if (nu  !== 6'd17) fails = fails + 1;  // unsigned-loop leading-one, bit 16 -> 17
      // negatives, hand-computed for vn = 0xB4 (set bits 2,4,5,7):
      if (e_step2  !== 6'd5)  fails = fails + 1;  // highest even set bit (4) + 1
      if (e_start1 !== 7'd8)  fails = fails + 1;  // highest set bit in [1,32) (7) + 1
      if (e_mul    !== 7'd15) fails = fails + 1;  // 2*7 + 1
      if (e_off    !== 6'd7)  fails = fails + 1;  // idx where vec[idx+1]; highest = 6 -> 7
      if (e_noP1   !== 6'd7)  fails = fails + 1;  // highest set bit (7), no +1
      if (e_narrow !== 6'd4)  fails = fails + 1;  // W != width: only low 16 bits scanned (bit 3)
      if (fails == 0) $write("*-* All Finished *-*\n");
      else $write("FAILED: %0d mismatches\n", fails);
      $finish;
    end
  end
endmodule
