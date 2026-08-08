// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Determinism: encounter-ordered walks
module sub (
  input  logic clk,
  input  logic [6:0] din,
  output logic [6:0] dout
);
  /*verilator no_inline_module*/
  logic [6:0] s1;  // reconstructed comb chain
  logic [6:0] s2;
  assign s1 = din + 7'h07;
  assign s2 = s1 ^ (din << 1);
  assign dout = s2;

  logic [6:0] wo;  // write-only register
  always_ff @(posedge clk) wo <= din + 7'h11;
endmodule

module t (
  input logic clk,
  input logic rst
);

  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;

  logic [6:0] keep;
  logic [6:0] result;
  logic [6:0] observe;

  // SCC cycles, aliases, self-loops
  logic [6:0] cyc_a;
  logic [6:0] cyc_b;
  assign cyc_a = cyc_b ^ keep;
  assign cyc_b = cyc_a ^ keep;

  logic [6:0] cyc_down;  // downstream of cycle
  assign cyc_down = cyc_a ^ cyc_b ^ keep;

  logic [6:0] ali_a;
  logic [6:0] ali_b;
  assign ali_a = ali_b;
  assign ali_b = ali_a;

  logic [6:0] self_loop;
  assign self_loop = self_loop & keep;

  logic [6:0] cmb1;  // continuous chain
  logic [6:0] cmb2;
  logic [6:0] cmb3;
  assign cmb1 = keep + 7'h7;
  assign cmb2 = cmb1 ^ 7'h2a;
  assign cmb3 = cmb2 + 7'h5;

  // Comb (unconditional, if/else, shadow-reads)
  logic [6:0] cf_uncond;
  always_comb cf_uncond = keep ^ 7'h11;

  logic [6:0] cf_ifelse;
  always_comb begin
    if (keep[0]) cf_ifelse = keep + 7'h1;
    else         cf_ifelse = keep - 7'h1;
  end

  logic [6:0] cf_readsrecon;
  always_comb cf_readsrecon = cmb1 ^ 7'h2;

  ps_t ps_comb;  // packed aggregates
  always_comb begin
    ps_comb.hi = keep[6:3];
    ps_comb.lo = keep[3:0];
  end

  logic [1:0][6:0] pa_comb;
  always_comb pa_comb = {keep, keep ^ 7'h5a};

  logic [7:0] cf_ctv;  // multi-range assembly
  assign cf_ctv[3:0] = keep[3:0];
  assign cf_ctv[7:4] = keep[6:3];

  ps_t cf_cts;
  assign cf_cts.hi = keep[3:0];
  assign cf_cts.lo = keep[6:3];

  logic [6:0] alias1;  // aliases
  logic [6:0] alias2;
  assign alias1 = keep;
  assign alias2 = alias1;

  logic [6:0] out0;  // multi-instance submodules
  logic [6:0] out1;
  sub u0 (.clk(clk), .din(keep),          .dout(out0));
  sub u1 (.clk(clk), .din(keep ^ 7'h3c), .dout(out1));

  always_ff @(posedge clk) begin
    if (rst) begin
      keep <= 7'h0;
      result <= 7'h0;
      observe <= 7'h0;
    end else begin
      keep <= keep + 7'h3;
      result <= cmb3;
      observe <= result ^ alias2 ^ out0 ^ out1 ^ cf_uncond ^ cf_ifelse
               ^ cf_readsrecon ^ ps_comb[6:0] ^ pa_comb[0] ^ cf_ctv[6:0]
               ^ cf_cts[6:0] ^ cyc_down ^ ali_a ^ self_loop;
    end
  end

endmodule
