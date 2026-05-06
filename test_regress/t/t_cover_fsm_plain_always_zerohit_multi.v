// DESCRIPTION: Verilator: FSM coverage keeps zero-hit records for near-miss plain always shapes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Group plain-always near misses that still recover enough structure to leave
// zero-hit FSM records behind, but must not warn or model a supported FSM.

module near_canonical_state_d_case (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;

  // Unsupported for the plain-always warning scan: case(state_d) is only
  // near-supported when it follows the canonical state_d = state_q default.
  always @(posedge clk) begin
    state_d = S1;
    case (state_d)
      S0: state_d = start ? S1 : S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module selector_matches_noassign (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic other;
  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;

  // The selector matches the FSM state, but the case body never assigns
  // state_d, so the warning scan should ignore it while leaving zero-hit
  // state points behind.
  always @(posedge clk) begin
    state_d = state_q;
    case (state_q)
      S0: other = start;
      default: other = 1'b0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module t (
    input logic clk
);
  logic rst;
  logic start;
  integer cyc;

  near_canonical_state_d_case near_canonical_state_d_case_u (.*);
  selector_matches_noassign selector_matches_noassign_u (.*);

  initial begin
    rst = 1'b1;
    start = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
