// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%p exp=%p (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0);
// verilog_format: on

// Combinational logic depending on more derived clocks than fit in one word of the trigger
// vector, so its trigger condition tests a whole word, alongside logic on the main clock.
module t (
    input clk
);
  localparam int N = 130;
  localparam int M = 48;

  function automatic logic [30:0] step(logic [30:0] v, int i);
    logic [30:0] r;
    r = {v[29:0], v[30] ^ v[27]};
    return r ^ (r >> (i % 7 + 1)) ^ 31'(i * 3);
  endfunction

  function automatic logic [30:0] expected(int i, int n);
    logic [30:0] v;
    v = 31'(i * 7 + 1);
    for (int k = 0; k < n; ++k) v = step(v, i);
    return v;
  endfunction

  int cyc = 0;
  // Johnson counter: each bit rises once every 2*N cycles, one bit per cycle
  logic [N-1:0] clks = '0;
  logic [N-1:0] expToggles = '0;
  logic [30:0] lfsr[M];

  wire [N-1:0] nextClks = {clks[N-2:0], ~clks[N-1]};
  wire [N-1:0] toggles;
  wire parity = ^toggles;

  for (genvar i = 0; i < N; ++i) begin : gen_clk
    logic q = 1'b0;
    always_ff @(posedge clks[i]) q <= ~q;
    assign toggles[i] = q;
  end

  for (genvar i = 0; i < M; ++i) begin : gen_lfsr
    always_ff @(posedge clk) lfsr[i] <= (cyc == 0) ? 31'(i * 7 + 1) : step(lfsr[i], i);
  end

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    clks <= nextClks;
    expToggles <= expToggles ^ (nextClks & ~clks);
    `checkh(toggles, expToggles);
    `checkh(parity, ^expToggles);
    if (cyc == N || cyc == 2 * N + 7) begin
      for (int i = 0; i < M; ++i) `checkh(lfsr[i], expected(i, cyc - 1));
    end
    if (cyc == 2 * N + 7) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
