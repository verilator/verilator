// DESCRIPTION: Verilator: FSM reporting coverage test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  integer cyc;
  logic rst;
  logic start;
  state_t state_default /*verilator fsm_arc_include_cond*/;
  state_t state_reset_incl /*verilator fsm_reset_arc*/;
  state_t state_reset_excl;

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
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // This FSM gives the reporting path both ordinary arcs and a synthetic
  // default arc so annotate/write-info exercise FSM-arc filtering.
  always_ff @(posedge clk) begin
    if (rst) begin
      state_default <= S0;
    end else begin
      case (state_default)
        S0: if (start) state_default <= S1; else state_default <= S2;
        default: state_default <= S0;
      endcase
    end
  end

  // These two FSMs give reporting both reset-include and reset-exclude arcs so
  // annotate can exercise the reset-arc filtering wording in both modes.
  always_ff @(posedge clk) begin
    if (rst) begin
      state_reset_incl <= S0;
    end else begin
      case (state_reset_incl)
        S0: state_reset_incl <= S1;
        default: state_reset_incl <= S1;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state_reset_excl <= S0;
    end else begin
      case (state_reset_excl)
        S0: state_reset_excl <= S1;
        default: state_reset_excl <= S1;
      endcase
    end
  end

endmodule
