// DESCRIPTION: Verilator: Shared subgraph logic scales across receivers
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0)
// verilog_format: on

module t #(
  parameter int N = 32,
  parameter bit BENCH = 0
) (
  input logic clk,
  output logic [31:0] checksum
);
  int unsigned cycles = 0;
  wire [6:0] q [N];

  for (genvar i = 0; i < N; ++i) begin : g
    sg_shared_scale child (.clk(clk), .d(7'(cycles + i)), .q(q[i]));
  end

  always_comb begin
    checksum = 0;
    for (int i = 0; i < N; ++i) checksum = (checksum * 32'd16777619) ^ 32'(q[i]);
  end

  always @(posedge clk) begin
    if (!BENCH) begin
      for (int i = 0; i < N; ++i) begin
        if (cycles == 0) begin
          `checkh(q[i], 7'd1);
        end else begin
          `checkh(q[i], 7'(cycles - 1 + i));
        end
      end
      if (cycles == 8) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    end
    cycles <= cycles + 1;
  end
endmodule

module sg_shared_scale (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q = 1
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= d;
endmodule
