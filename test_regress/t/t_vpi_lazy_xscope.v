// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Cross-scope ports must retain independent deposit semantics.

module t (
  input logic clk,
  input logic rst,
  input logic [31:0] in,
  output logic [31:0] out
);

  logic [31:0] acc;
  logic [31:0] accn;
  logic [31:0] canon;
  logic [31:0] canonr;
  logic [31:0] qa;
  logic [31:0] qb;
  logic [31:0] qc;
  logic [31:0] qd;
  logic [31:0] qe;
  logic [31:0] qf;
  logic [31:0] qg;
  logic [31:0] qh;

  always_comb accn = rst ? 32'd0 : acc + in;

  always_ff @(posedge clk) begin
    acc <= accn;
    canonr <= accn ^ 32'ha5a5_a5a5;
  end

  always_comb canon = acc ^ 32'h5a5a_5a5a;

  // Real and string ports cannot use a cross-scope memcpy row.
  real   rcanonr;
  string scanonr;
  always_ff @(posedge clk) begin
    rcanonr <= $itor(accn) + 0.25;
    scanonr <= accn[0] ? "odd" : "even";
  end

  xsub u_a(.p(canon), .q(qa));
  xsub u_b(.p(canon), .q(qb));
  xsubr u_c(.p(canonr), .q(qc));
  xsubr u_d(.p(canonr), .q(qd));
  xsubre u_e(.p(rcanonr), .q(qe));
  xsubre u_f(.p(rcanonr), .q(qf));
  xsubse u_g(.p(scanonr), .q(qg));
  xsubse u_h(.p(scanonr), .q(qh));

  assign out = qa ^ qb ^ qc ^ qd ^ qe ^ qf ^ qg ^ qh;

endmodule

// Not inlined so the port keeps its parent-scope driver.
// against both drivers would retain for all of them and cover neither.
module xsub (
  input logic [31:0] p,
  output logic [31:0] q
);
  /* verilator no_inline_module */

  assign q = p + 32'd7;

endmodule

module xsubr (
  input logic [31:0] p,
  output logic [31:0] q
);
  /* verilator no_inline_module */

  assign q = p + 32'd7;

endmodule

module xsubre (
  input real p,
  output logic [31:0] q
);
  /* verilator no_inline_module */

  assign q = $rtoi(p) + 32'd7;

endmodule

module xsubse (
  input string p,
  output logic [31:0] q
);
  /* verilator no_inline_module */

  always_comb q = 32'(p.len());

endmodule
