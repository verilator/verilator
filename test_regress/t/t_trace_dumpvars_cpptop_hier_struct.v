// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

typedef struct packed {
  logic [31:0] add;
  logic [31:0] cyc;
  logic [31:0] inner;
} deep_t;

typedef struct packed {
  deep_t deep;
  logic [31:0] value;
} top_t;

module t(
    input clk
);
  int cyc;
  top_t mystruct;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    // Test $dumpvars with a traced struct sub-scope via cpptop.
    $dumpvars(1, cpptop.t.mystruct.deep);
  end

  always_comb begin
    mystruct.value = cyc + 32'd10;
    mystruct.deep.add = 32'd11;
    mystruct.deep.cyc = cyc;
    mystruct.deep.inner = cyc + mystruct.deep.add;
  end
endmodule
