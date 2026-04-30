// DESCRIPTION: Verilator: FSM coverage begin-wrapped/if-else test
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic rst;
  logic sel;
  int cyc;
  state_t state  /*verilator fsm_reset_arc*/;

  initial begin
    rst = 1'b1;
    sel = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state <= S0;
    end
    else begin
      case (state)
        S0: begin
          if (sel) begin
            state <= S1;
          end
          else begin
            state <= S2;
          end
        end
        S1: begin
          state <= S0;
        end
        default: begin
          state <= S0;
        end
      endcase
    end
  end

endmodule
