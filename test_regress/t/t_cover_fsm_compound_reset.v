// DESCRIPTION: Verilator: FSM coverage with a compound reset and line and expression coverage
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  typedef enum logic [1:0] {
    IDLE,
    RUN,
    DONE
  } state_t;

  state_t state;
  state_t state_next;
  logic rst;
  logic flush;
  logic go;
  logic last;
  state_t state2;
  state_t state2_next;
  int cyc;

  // Reset and flush share the reset branch, as in a pipeline stage that
  // returns to IDLE on either.
  always_ff @(posedge clk) begin
    if (rst | flush) state <= IDLE;
    else state <= state_next;
  end

  // The same reset as a conditional, which expression coverage instruments
  always_ff @(posedge clk) begin
    state2 <= (rst | flush) ? IDLE : state2_next;
  end

  always_comb begin
    case (state2)
      IDLE:
      if (go) state2_next = RUN;
      else state2_next = IDLE;
      RUN: state2_next = DONE;
      default: state2_next = IDLE;
    endcase
  end

  always_comb begin
    case (state)
      IDLE:
      if (go) state_next = RUN;
      else state_next = IDLE;
      RUN:
      if (last) state_next = DONE;
      else state_next = RUN;
      DONE: state_next = IDLE;
      default: state_next = IDLE;
    endcase
  end

  initial cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    rst <= (cyc == 0);
    flush <= (cyc == 4);
    go <= (cyc == 1) || (cyc == 5);
    last <= (cyc == 7);
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
