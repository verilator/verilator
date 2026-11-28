// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  typedef enum logic [1:0] {
    S0,
    S1,
    S2,
    S3
  } state_t;

  state_t state_q;
  state_t state_d;
  logic [3:0] seen;
  logic rst;
  int cyc;

  always_comb begin
    seen = '0;
    seen[state_q] = 1'b1;
    state_d = (state_q == S0) ? S1 : (state_q == S1) ? S2 : (state_q == S2) ? S3 : S0;
  end

  always_ff @(posedge clk) state_q <= rst ? S0 : state_d;

  initial cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    rst <= (cyc == 0) || (cyc == 6);
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
