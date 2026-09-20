// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  int cyc = 0;

`ifdef LIMIT_DEPTH
  covergroup cg with function sample (bit [1024:0] value);
    cp: coverpoint value {
      bins whole = {[$ : $]};
      ignore_bins endpoints = {1025'b0, {1025{1'b1}}};
    }
  endgroup
`elsif LIMIT_PRODUCT
  covergroup cg with function sample (bit [5:0] value);
    a: coverpoint value {
      ignore_bins removed = {0};
    }
    b: coverpoint value;
    c: coverpoint value;
    d: coverpoint value;
    e: coverpoint value;
    f: coverpoint value;
    cx: cross a, b, c, d, e, f;
  endgroup
`else
  localparam logic [63:0] ANY = 64'bx;
  covergroup cg with function sample (bit [63:0] value, bit side);
    cp: coverpoint value {
      bins whole = {[$ : $]};
      wildcard ignore_bins pairs = {
        ANY & ~64'h0000000100000001, ANY & ~64'h0000000200000002,
        ANY & ~64'h0000000400000004, ANY & ~64'h0000000800000008,
        ANY & ~64'h0000001000000010, ANY & ~64'h0000002000000020,
        ANY & ~64'h0000004000000040, ANY & ~64'h0000008000000080,
        ANY & ~64'h0000010000000100, ANY & ~64'h0000020000000200,
        ANY & ~64'h0000040000000400, ANY & ~64'h0000080000000800,
        ANY & ~64'h0000100000001000, ANY & ~64'h0000200000002000,
        ANY & ~64'h0000400000004000, ANY & ~64'h0000800000008000,
        ANY & ~64'h0001000000010000, ANY & ~64'h0002000000020000,
        ANY & ~64'h0004000000040000, ANY & ~64'h0008000000080000,
        ANY & ~64'h0010000000100000, ANY & ~64'h0020000000200000,
        ANY & ~64'h0040000000400000, ANY & ~64'h0080000000800000
      };
`ifndef LIMIT_QUERY
      ignore_bins endpoint = {64'hffffffffffffffff};
`endif
    }
`ifdef LIMIT_QUERY
    other: coverpoint side {
      bins zero = {0};
    }
    cx: cross cp, other{bins selected = binsof (cp) intersect {[0 : 64'hfffffffefffffffe]};}
`endif
  endgroup
`endif

  cg cov;

  always @(posedge clk) begin
    ++cyc;
    if (cyc == 3) cov = new;
    if (cyc == 4) $fatal(1, "Expected a covergroup construction limit");
  end
endmodule
