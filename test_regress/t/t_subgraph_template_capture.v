// DESCRIPTION: Verilator: Shared subgraph input captures preserve old output values
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
  int unsigned cycles = 0;
  wire [6:0] a;
  wire [6:0] b;

  sg_template_capture i_a (.clk(clk), .d(b + 7'd1), .q(a));
  sg_template_capture i_b (.clk(clk), .d(7'd42), .q(b));

  always @(posedge clk) begin
    if (cycles == 0) begin
      `checkh(a, 1);
      `checkh(b, 1);
    end else if (cycles == 1) begin
      `checkh(a, 2);
      `checkh(b, 42);
    end else begin
      `checkh(a, 43);
      `checkh(b, 42);
    end
    cycles <= cycles + 1;
    if (cycles == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module sg_template_capture (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q = 1
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= d;
endmodule
