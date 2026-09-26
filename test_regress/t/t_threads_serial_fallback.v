// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%p exp=%p (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0);
// verilog_format: on

// Heavy logic on the rising edge runs in parallel, while passes that only
// trigger the light falling-edge logic run sequentially.
module t (
    input clk
);
  localparam int N = 48;

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
  int negCount = 0;
  logic [30:0] lfsr[N];

  for (genvar i = 0; i < N; ++i) begin : gen
    always_ff @(posedge clk) lfsr[i] <= (cyc == 0) ? 31'(i * 7 + 1) : step(lfsr[i], i);
  end

  always_ff @(negedge clk) negCount <= negCount + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc > 1) `checkd(negCount, cyc);
    if (cyc == 20 || cyc == 57 || cyc == 99) begin
      for (int i = 0; i < N; ++i) `checkh(lfsr[i], expected(i, cyc - 1));
    end
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
