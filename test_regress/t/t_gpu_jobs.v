// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Eduardo Schwarz Danni
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  import "DPI-C" function int job_seed();

  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;
  int limit = 0;
  int seed = 0;
  logic [30:0] lfsr = 0;

  function automatic logic [30:0] model(int start, int steps);
    logic [30:0] v = 31'(start);
    for (int i = 1; i < steps; ++i) v = {v[29:0], v[30] ^ v[27]};
    return v;
  endfunction

  initial begin
    if (!$value$plusargs("limit=%d", limit)) limit = 20;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      seed <= job_seed();
      lfsr <= 31'(job_seed());
    end else begin
      lfsr <= {lfsr[29:0], lfsr[30] ^ lfsr[27]};
    end
    if (cyc == limit) begin
      $display("seed=%0d cyc=%0d lfsr=%0d time=%0t", seed, cyc, lfsr, $time);
      `checkd(lfsr, model(seed, limit));
      if (seed == 5) `stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
