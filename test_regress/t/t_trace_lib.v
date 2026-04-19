// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`ifdef TOP
module t (
    input clk
);

  logic [7:0] in0 = 8'd020;
  logic [7:0] in1 = 8'd100;
  wire [7:0] out0;
  wire [7:0] out1;
  int count = 0;

  sub0 i_sub0 (
      .clk(clk),
      .in(in0),
      .out(out0)
  );
  sub1 i_sub1 (
      .clk(clk),
      .in(in1),
      .out(out1)
  );

  always_ff @(posedge clk) begin
    count <= count + 1;
    in0 <= in0 + 8'd1;
    in1 <= in1 + 8'd2;
    if (count == 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
`endif

`ifdef SUB0
module sub0 (
    input wire clk,
    input wire [7:0] in,
    output wire [7:0] out
);

  logic [7:0] ff;
  always_ff @(posedge clk) ff <= in + 8'd1;
  assign out = ff;

endmodule
`endif

`ifdef SUB1
module sub1 (
    input wire clk,
    input wire [7:0] in,
    output wire [7:0] out
);

  logic [7:0] ff;
  always_ff @(posedge clk) ff <= in + 8'd2;
  assign out = ff;

endmodule
`endif
