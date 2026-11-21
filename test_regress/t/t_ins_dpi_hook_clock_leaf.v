// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Leaves next to a clock leaf of the same variable (clks[1] next to clks[0], p.b next to p.c),
// and leaves two path steps deep (s2.in.x, s3.arr[1].x)
module top_module;
  typedef struct packed {
    logic       c;
    logic [6:0] b;
  } pk_t;
  typedef struct {logic [7:0] x;} in_t;
  typedef struct {in_t in;} out_t;
  typedef struct {in_t arr[2];} arr_t;

  logic clks[2] = '{1'b0, 1'b0};
  pk_t  p = '{c: 1'b0, b: 7'h00};
  out_t s2 = '{in: '{x: 8'h00}};
  arr_t s3 = '{arr: '{'{x: 8'h00}, '{x: 8'h00}}};
  int   cyc = 0;
  int   pcnt = 0;

  always #5 clks[0] = ~clks[0];
  always #5 p.c = ~p.c;

  always @(posedge p.c) pcnt <= pcnt + 1;

  always @(posedge clks[0]) begin
    cyc <= cyc + 1;
    clks[1] <= cyc[0];
    p.b <= 7'h20 + cyc[6:0];
    s2.in.x <= 8'h30 + cyc[7:0];
    s3.arr[1].x <= 8'h40 + cyc[7:0];
    $display("$[%0d| clks[1]: %0d p.b: %02x s2.in.x: %02x s3.arr[1].x: %02x pcnt: %0d]", cyc,
             clks[1], p.b, s2.in.x, s3.arr[1].x, pcnt);
    if (cyc > 6) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
