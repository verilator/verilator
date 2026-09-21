// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// '$c(1)' keeps an expression impure, so --vpi-lazy retains its target with storage.
`define IMPURE_ONE ($c(1))

module t (
  input logic clk,
  input logic rst,
  output logic [7:0] observe
);

  // Retained by --vpi-lazy, so writable only through VPI; 'gated' is deposited into,
  // 'quiet' never is
  logic [7:0] gated;
  logic [7:0] quiet;
  logic [7:0] flopped;

  // Retained comb consumers, so their storage is a real observable
  logic [7:0] consumer;
  logic [7:0] quiet_cons;
  always_comb consumer = gated ^ 8'(8'h5a * `IMPURE_ONE);
  always_comb quiet_cons = quiet + 8'(8'h11 * `IMPURE_ONE);

  // Counts evaluations of each retained signal's consumer cone
  always_comb $c("{ extern int vlConsEvals; ++vlConsEvals; (void)", consumer, "; }");
  always_comb $c("{ extern int vlQuietEvals; ++vlQuietEvals; (void)", quiet_cons, "; }");

  always_ff @(posedge clk) begin
    if (rst) begin
      gated <= 8'h0;
      quiet <= 8'h0;
      flopped <= 8'h0;
    end else begin
      gated <= gated + 8'h3;
      quiet <= quiet + 8'h5;
      flopped <= consumer;
    end
  end

  assign observe = flopped ^ quiet_cons;

endmodule
