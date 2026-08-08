// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Inlined for retargeting path
module sub2 (
  input  logic [6:0] p2_in,
  output logic [6:0] p2_out
);
  assign p2_out = p2_in ^ 7'h15;
endmodule

module sub (
  input  logic [6:0] sub_in,
  output logic [6:0] sub_out
);
  sub2 u_sub2 (.p2_in(sub_in), .p2_out(sub_out));
endmodule

module t (
  input  logic clk,
  input  logic rst,
  output logic [6:0] observe
);

  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;

  // Boundary registers
  logic [6:0] keep;
  logic signed [6:0] skeep;
  logic [69:0] wkeep;  // >64 bits, exercises wide reconstruction
  logic [6:0] result;

  logic [6:0] cmb1;
  logic [6:0] cmb2;
  logic [6:0] cmb3;
  assign cmb1 = keep + 7'h7;
  assign cmb2 = cmb1 ^ 7'h2a;
  assign cmb3 = cmb2 + 7'h5;

  logic signed [6:0] scmb;
  assign scmb = skeep - 7'sd3;

  logic [69:0] wcmb;  // >64 bits
  assign wcmb = wkeep + 70'd1;

  logic bsel;  // Sel/Cond/>>> operators
  assign bsel = keep[2];

  logic [6:0] mux0;
  assign mux0 = keep[0] ? cmb1 : cmb2;

  logic [6:0] psel;
  assign psel = {mux0[3:0], keep[6:4]};

  logic signed [6:0] sshift;
  assign sshift = skeep >>> 2;

  logic [69:0] wsel;  // select-from-wide
  assign wsel = {wkeep[66:0], wkeep[69:67]};

  logic [6:0] alias1;  // aliases
  logic [6:0] alias2;
  assign alias1 = keep;
  assign alias2 = alias1;

  logic [6:0] sub_out;
  sub u_sub (.sub_in(keep), .sub_out(sub_out));

  // Comb folds
  logic [6:0] pcomb;
  always_comb pcomb = keep ^ result;

  logic [6:0] cf_uncond;
  always_comb cf_uncond = keep ^ 7'h11;

  logic [6:0] cf_ifelse;
  always_comb begin
    if (keep[0]) cf_ifelse = keep + 7'h1;
    else         cf_ifelse = keep - 7'h1;
  end

  logic [6:0] cf_ifdef;
  always_comb begin
    cf_ifdef = keep + 7'h4;
    if (keep[1]) cf_ifdef = ~keep;
  end

  logic [6:0] cf_readsrecon;
  always_comb cf_readsrecon = cmb1 ^ 7'h2;

  logic [6:0] cf_readscomb;
  always_comb cf_readscomb = cf_uncond + 7'h3;

  logic [6:0] cf_case;
  always_comb begin
    case (keep[1:0])
      2'd0: cf_case = keep;
      2'd1: cf_case = keep + 7'h1;
      2'd2: cf_case = keep + 7'h2;
      default: cf_case = keep + 7'h3;
    endcase
  end

  logic [6:0] cf_partial;
  always_comb begin
    cf_partial = 7'h0;
    cf_partial[3:0] = keep[3:0];
  end

  logic [7:0] cf_vlsb;
  always_comb begin
    cf_vlsb = {keep, 1'b0};
    cf_vlsb[keep[1:0]*2 +: 2] = skeep[1:0];
  end

  logic [6:0] cf_casepart;
  always_comb begin
    cf_casepart = keep;
    case (keep[1:0])
      2'd0: cf_casepart = keep + 7'h1;
      2'd1: cf_casepart[3:0] = skeep[3:0];
      default: cf_casepart = ~keep;
    endcase
  end

  logic [6:0] cf_mta;
  logic [6:0] cf_mtb;
  always_comb begin
    cf_mta = keep + 7'h6;
    cf_mtb = cf_mta ^ 7'h1;
  end

  // Tier B: multi-range partial assembly
  logic [7:0] cf_ctv;
  assign cf_ctv[3:0] = keep[3:0];
  assign cf_ctv[7:4] = skeep[3:0];

  ps_t cf_cts;
  assign cf_cts.hi = keep[3:0];
  assign cf_cts.lo = skeep[3:0];

  // Mixed full+partial, overlapping (retained)
  /* verilator lint_off MULTIDRIVEN */
  logic [6:0] cf_mixfull;
  assign cf_mixfull = keep;
  assign cf_mixfull[2:0] = skeep[2:0];

  logic [6:0] cf_ovl;
  assign cf_ovl[4:0] = keep[4:0];
  assign cf_ovl[6:2] = skeep[4:0];
  /* verilator lint_on MULTIDRIVEN */

  // Shapes that bail fold
  /* verilator lint_off LATCH */
  logic [6:0] cf_nopre;
  always_comb begin
    cf_nopre[3:0] = keep[3:0];
  end
  /* verilator lint_on LATCH */

  // Genuine latch
  /* verilator lint_off LATCH */
  logic [6:0] cf_latch;
  always_comb begin
    if (keep[2]) cf_latch = keep;
  end
  /* verilator lint_on LATCH */

  logic [6:0] cf_selfread;  // self-read target
  always_comb begin
    cf_selfread = keep;
    cf_selfread = cf_selfread + 7'h1;
  end

  logic [6:0] cf_portop;  // port-read candidate
  assign cf_portop = rst ? 7'h0 : keep;

  // Write-only registers
  logic [6:0]  wo_plain;
  logic signed [6:0]  wo_signed;
  logic [69:0] wo_wide;

  always_ff @(posedge clk) begin
    if (rst) begin
      keep <= 7'h0;
      skeep <= 7'sh0;
      wkeep <= 70'h0;
      result <= 7'h0;
      wo_plain <= 7'h0;
      wo_signed <= 7'sh0;
      wo_wide <= 70'h0;
      observe <= 7'h0;
    end else begin
      keep <= keep + 7'h3;
      skeep <= skeep - 7'sd2;
      wkeep <= wkeep + 70'd5;
      result <= cmb3;
      wo_plain  <= keep + 7'h9;
      wo_signed <= skeep - 7'sd1;
      wo_wide   <= wkeep + 70'd11;
      observe <= result ^ alias2 ^ sub_out ^ pcomb ^ cf_uncond ^ cf_ifelse
               ^ cf_ifdef ^ cf_readsrecon ^ cf_readscomb ^ cf_case
               ^ cf_partial ^ cf_vlsb[6:0] ^ cf_casepart ^ cf_mta ^ cf_mtb
               ^ cf_nopre ^ cf_latch ^ cf_selfread
               ^ cf_ctv[6:0] ^ {cf_cts[6:0]} ^ cf_mixfull ^ cf_ovl;
    end
  end

endmodule
