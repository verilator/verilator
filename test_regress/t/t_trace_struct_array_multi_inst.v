// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test that arrays of structs with nested sub-members produce
// correct aliases (not empty scopes) across module instances.

module t (
    input clk
);

  int cnt;

  initial cnt = 0;
  always @(posedge clk) begin
    cnt <= cnt + 1;
    if (cnt == 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  sub sub_a (.clk, .seed(cnt));
  sub sub_b (.clk, .seed(cnt + 100));
endmodule

module sub (
    input clk,
    input int seed
);

  typedef struct packed {
    logic [7:0] x;
    logic [7:0] y;
  } inner_t;

  typedef struct packed {
    inner_t sub;
    logic [1:0] [7:0] arr;
    logic [7:0] simple;
  } outer_t;

  // Unpacked array of struct with nested sub-struct and packed array
  outer_t uarr [1:0];

  always @(posedge clk) begin
    uarr[0] <= '{sub: '{x: seed[7:0], y: seed[15:8]},
                 arr: '{seed[7:0], seed[7:0]+8'd1},
                 simple: seed[7:0]};
    uarr[1] <= '{sub: '{x: ~seed[7:0], y: ~seed[15:8]},
                 arr: '{~seed[7:0], ~seed[7:0]+8'd1},
                 simple: ~seed[7:0]};
  end
endmodule
