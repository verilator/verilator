// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(g,e) do if ((g) !== (e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)
// verilog_format: on

module t;
  bit [64:0] source_value;
  wire single_copy[2];
  wire [6:0] narrow_copy[2];
  wire [64:0] wide_copy[2];

  chain #(
      .WIDTH(1)
  ) single_chain (
      source_value[0],
      single_copy
  );
  chain #(
      .WIDTH(7)
  ) narrow_chain (
      source_value[6:0],
      narrow_copy
  );
  chain #(
      .WIDTH(65)
  ) wide_chain (
      source_value,
      wide_copy
  );

  initial begin
    for (int cycle = 0; cycle < 6; ++cycle) begin
      source_value = 65'h1_1234_5678_9abc_def0 ^ 65'(cycle * 13);
      #1;
      foreach (single_copy[i]) begin
        `checkh(single_copy[i], source_value[0]);
        `checkh(narrow_copy[i], source_value[6:0]);
        `checkh(wide_copy[i], source_value);
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module chain #(
    parameter int WIDTH = 1
) (
    input bit [WIDTH-1:0] src,
    output wire [WIDTH-1:0] b[2]
);
  wire [WIDTH-1:0] a[2]  /* verilator forceable */;
  assign a[0] = src;
  assign a[1] = b[0];
  assign b = a;
endmodule
