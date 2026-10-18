// DESCRIPTION: Verilator: FSM coverage after matchIfSameLast optimization
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Hudson River Trading LLC
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input logic clk
);
  typedef enum logic [1:0] { IDLE, RUN, DONE } state_t;
  state_t state;
  int cyc = 0;
  // Reset again from RUN on the last cycle.
  wire rst = cyc == 0 || cyc == 11;
  wire enable = cyc[0];

  always_ff @(posedge clk) begin
    if (rst) state <= IDLE;
    else begin
      unique case (state)
        IDLE: begin
          // Both arms must remain covered after their common assignment moves.
          // The IDLE -> RUN arc must be present with four hits.
          if (enable) state <= RUN;
          else state <= RUN;
        end
        RUN: state <= DONE;
        DONE: state <= IDLE;
      endcase
    end
  end

  // verilator coverage_off
  always @(posedge clk) cyc <= cyc + 1;

  always @(negedge clk) begin
    if (cyc != 0) begin
      `checkd(int'(state), cyc == 12 ? int'(IDLE) : (cyc - 1) % 3);
      if (cyc == 12) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    end
  end
endmodule
