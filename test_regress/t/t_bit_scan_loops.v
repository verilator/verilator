// DESCRIPTION: Verilator: Verilog Test module
//
// Exercises the bit-counting loop idioms that V3Unroll lowers to builtins:
//   leading-one   for (b=0;b<W;b++) if (vec[b]) n = b + 1;   -> $mostsetbitp1(vec)
//   count-ones    for (b=0;b<W;b++) if (vec[b]) n = n + 1;   -> $countones(vec)
// Positives must lower (counted via --stats by the .py); negatives compute a
// different value than the builtin and so must be left as loops.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  // ---- positives: must lower ----
  logic [31:0] p32;
  logic [5:0] n32;  // I path, narrow target (select resize)
  logic [47:0] p48;
  logic [6:0] n48;  // Q path
  logic [79:0] p80;
  logic [6:0] n80;  // W path
  logic [31:0] pu;
  logic [5:0] nu;  // unsigned loop index
  logic [31:0] p32e;
  logic [31:0] n32e;  // 32-bit target (no resize)
  logic [31:0] p32w;
  logic [39:0] n40;  // >32-bit target (extend resize)
  logic [31:0] pc;
  logic [5:0] nc;  // count-ones -> $countones
  logic [31:0] kvec;  // const (set in initial) -> exercises $mostsetbitp1 fold
  logic [5:0] kn;
  initial kvec = 32'h0000_0100;
  logic [31:0] kvec0;  // const 0 -> $mostsetbitp1(0)=0 (covers the zero path)
  logic [5:0] kn0;
  initial kvec0 = 32'h0;
  always_comb begin
    n32 = 0;
    for (int b = 0; b < 32; b++) if (p32[b]) n32 = 6'(b + 1);
  end
  always_comb begin
    n48 = 0;
    for (int b = 0; b < 48; b++) if (p48[b]) n48 = 7'(b + 1);
  end
  always_comb begin
    n80 = 0;
    for (int b = 0; b < 80; b++) if (p80[b]) n80 = 7'(b + 1);
  end
  always_comb begin
    nu = 0;
    for (int unsigned b = 0; b < 32; b++) if (pu[b]) nu = 6'(b + 1);
  end
  always_comb begin
    n32e = 0;
    for (int b = 0; b < 32; b++) if (p32e[b]) n32e = 32'(b + 1);
  end
  always_comb begin
    n40 = 0;
    for (int b = 0; b < 32; b++) if (p32w[b]) n40 = 40'(b + 1);
  end
  always_comb begin
    nc = 0;
    for (int b = 0; b < 32; b++) if (pc[b]) nc = nc + 1;
  end
  always_comb begin
    kn = 0;
    for (int b = 0; b < 32; b++) if (kvec[b]) kn = 6'(b + 1);
  end
  always_comb begin
    kn0 = 0;
    for (int b = 0; b < 32; b++) if (kvec0[b]) kn0 = 6'(b + 1);
  end

  // ---- negatives: must NOT lower (each yields a different value than the builtin) ----
  logic [31:0] vn;  // shared input, bits {2,4,5,7}
  logic [31:0] vw;  // has a set bit above the scan bound
  logic [31:0] vt;  // for the truncated-index case
  logic en1;  // runtime gate for the compound-condition case
  logic [5:0] e_step2;
  logic [6:0] e_start1;
  logic [6:0] e_mul;
  logic [5:0] e_off;
  logic [5:0] e_noP1;
  logic [5:0] e_narrow;
  logic [5:0] e_comp;
  logic [5:0] e_trunc;
  always_comb begin
    e_step2 = 0;
    for (int b = 0; b < 32; b += 2) if (vn[b]) e_step2 = 6'(b + 1);
  end
  always_comb begin
    e_start1 = 0;
    for (int b = 1; b < 32; b++) if (vn[b]) e_start1 = 7'(b + 1);
  end
  always_comb begin
    e_mul = 0;
    for (int b = 0; b < 32; b++) if (vn[b]) e_mul = 7'(2 * b + 1);
  end
  always_comb begin
    e_off = 0;
    for (int b = 0; b < 31; b++) if (vn[b+1]) e_off = 6'(b + 1);
  end
  always_comb begin
    e_noP1 = 0;
    for (int b = 0; b < 32; b++) if (vn[b]) e_noP1 = 6'(b);
  end
  always_comb begin
    e_narrow = 0;
    for (int b = 0; b < 16; b++) if (vw[b]) e_narrow = 6'(b + 1);
  end
  always_comb begin
    e_comp = 0;
    for (int b = 0; b < 32; b++) if (vn[b] && en1) e_comp = 6'(b + 1);
  end
  // verilator lint_off WIDTHEXPAND
  always_comb begin
    e_trunc = 0;
    for (int b = 0; b < 32; b++) if (vt[b[2:0]]) e_trunc = 6'(b + 1);
  end
  // verilator lint_on WIDTHEXPAND

  int cyc = 0;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      p32 <= 32'h8000_0000;
      p48 <= 48'h0;
      p48[47] <= 1'b1;
      p80 <= 80'h0;
      p80[79] <= 1'b1;
      pu <= 32'h0001_0000;  // bit 16
      p32e <= 32'h8000_0000;
      p32w <= 32'h8000_0000;
      pc <= 32'hf0f0_f0f0;  // 16 ones
      vn <= 32'h0000_00b4;  // bits {2,4,5,7}
      vw <= 32'h0010_0008;  // bits {3,20}
      vt <= 32'h0000_0080;  // bit 7
      en1 <= 1'b0;  // gate off -> compound loop yields 0
    end
    else if (cyc == 1) begin
      `checkh(n32, 6'd32);
      `checkh(n48, 7'd48);
      `checkh(n80, 7'd80);
      `checkh(nu, 6'd17);  // unsigned-index leading-one, bit 16 -> 17
      `checkh(n32e, 32'd32);
      `checkh(n40, 40'd32);
      `checkh(nc, 6'd16);  // popcount(0xF0F0F0F0)
      `checkh(kn, 6'd9);  // mostsetbitp1(0x100), constant-folded
      `checkh(kn0, 6'd0);  // mostsetbitp1(0)=0, constant-folded (zero path)
      // negatives, hand-computed for vn = 0xB4 (bits 2,4,5,7):
      `checkh(e_step2, 6'd5);  // highest even set bit (4) + 1
      `checkh(e_start1, 7'd8);  // highest set bit in [1,32) (7) + 1
      `checkh(e_mul, 7'd15);  // 2*7 + 1
      `checkh(e_off, 6'd7);  // idx where vec[idx+1]; highest 6 -> 7
      `checkh(e_noP1, 6'd7);  // highest set bit (7), no +1
      `checkh(e_narrow, 6'd4);  // W=16 != width(vec): only low bits scanned (bit 3)
      `checkh(e_comp, 6'd0);  // && en1 (=0); a wrong lowering would give 8
      `checkh(e_trunc, 6'd32);  // vt[b[2:0]] last hits b=31; a wrong lowering would give 8
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
