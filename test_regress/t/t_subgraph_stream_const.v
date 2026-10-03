// DESCRIPTION: Verilator: Subgraph streaming operator constant test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while (0)
// verilog_format: on

module t (
  input logic clk
);

  int cyc;
  logic [30:0] ref_value;
  logic [30:0] value;

  sg_stream i_sg (clk, value);
  sg_stream_ref i_ref (clk, ref_value);

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc > 2) `checkh(value, ref_value);
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sg_stream (
  input logic clk,
  output logic [30:0] value
);
  /*verilator subgraph_boundary*/

  typedef logic [30:0] state_t;
  state_t state = 31'h1234_5678;

  assign value = state;
  always_ff @(posedge clk) state <= state_t'({<<8{state}}) ^ 31'h1020_4081;

endmodule

module sg_stream_ref (
  input logic clk,
  output logic [30:0] value
);

  typedef logic [30:0] state_t;
  state_t state = 31'h1234_5678;

  assign value = state;
  always_ff @(posedge clk) state <= state_t'({<<8{state}}) ^ 31'h1020_4081;

endmodule
