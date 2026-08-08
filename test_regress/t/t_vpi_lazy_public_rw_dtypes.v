// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// BasicDType (real/integer/enum/string) + packed aggregates reconstruct
module t (
  input logic clk,
  input logic [7:0] in0,
  output logic [7:0] obs
);

  typedef enum logic [1:0] { A, B, C, D } e_t;
  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;
  typedef struct { logic [7:0] a; logic [7:0] b; } us_t;

  // BasicDType kinds
  real    r_comb;    always_comb r_comb = 1.5;
  integer i_comb;    always_comb i_comb = in0 + 1;
  e_t     en_comb;   always_comb en_comb = e_t'(in0[1:0]);
  string  s_var;     always_comb s_var = "hi";
  logic [6:0] v_comb; always_comb v_comb = in0[6:0] ^ 7'h5;

  string  s_fmt;     always_comb s_fmt = $sformatf("v%0d", in0);  // $sformatf: fold bails

  // Packed aggregates
  ps_t    ps_comb;   always_comb begin ps_comb.hi = in0[7:4]; ps_comb.lo = in0[3:0]; end
  logic [3:0][7:0] pa_comb;
  always_comb pa_comb = {in0, in0 ^ 8'hff, in0 + 8'd1, in0 - 8'd1};

  // Unpacked aggregates
  us_t    us_comb;   always_comb begin us_comb.a = in0; us_comb.b = ~in0; end
  logic [7:0] mem [0:3];
  always_comb begin mem[0]=in0; mem[1]=in0+1; mem[2]=in0+2; mem[3]=in0+3; end

  assign obs = v_comb ^ i_comb[7:0] ^ mem[0] ^ ps_comb ^ pa_comb[0] ^ us_comb.a
             ^ {6'b0, en_comb} ^ {7'b0, s_fmt.len() != 0};

endmodule
