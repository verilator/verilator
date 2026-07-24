// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Cover fold/retain branches in classifier; compile-only.
module top(input clk,
           input [7:0] a, input [7:0] b, input [2:0] sel, input en,
           output [255:0] obus);

   logic [7:0] troot, lz_root;
   always_comb begin
      troot = a & b;
      lz_root = troot;
   end

   logic [7:0] ttp, lz_tp;
   always_comb begin
      ttp = a;
      ttp[3:0] = b[3:0];
      lz_tp = ttp;
   end

   logic [7:0] tpf, lz_pf;
   always_comb begin
      tpf[3:0] = a[3:0];
      lz_pf = tpf;
   end

   logic [7:0] uarr [0:1];
   logic [7:0] lz_nv;
   always_comb begin
      uarr[0] = a;
      lz_nv = uarr[0] ^ b;
   end

   logic [7:0] ttb, lz_tb;
   always_comb begin
      ttb = 8'h0;
      if (sel[0]) ttb = a;
      lz_tb = ttb + b;
   end

   logic [7:0] trbw, lz_rbw;
   always_comb begin
      lz_rbw = trbw;
      trbw = a | b;
   end

   logic [7:0] lz_ifc;
   logic tc;
   always_comb begin
      lz_ifc = a;
      if (tc) lz_ifc = b;
      tc = sel[1];
   end

   // Impure RHS ($c) bails fold.
   logic [7:0] lz_imp;
   always_comb lz_imp = a + $c8("0");

   logic [7:0] mixp;
   assign mixp[3:0] = a[3:0];
   always_comb mixp[7:4] = b[3:0];

   // Multi-driven comb (retained).
   logic [7:0] two;
   always_comb two = a;
   always_comb two = b;

   logic [7:0] disj;
   assign disj[3:0] = a[3:0];
   assign disj[7:4] = b[3:0];

   assign obus = {lz_root, lz_tp, lz_pf, lz_nv, lz_tb, lz_rbw, lz_ifc,
                  lz_imp, mixp, two, disj, {21{8'h0}}};
endmodule
