// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(
    input clk
);
  typedef struct packed {
    logic [7:0] \x ;
    logic [7:0] y;
  } point_t;

  typedef struct packed {
    point_t origin;
    point_t size;
  } rect_t;

  int cyc;
  rect_t rect;
  point_t \pt ;

  sub #(10) sub_a(.*);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    \pt .\x  <= \pt .\x  + 1;
    \pt .y <= \pt .y + 2;
    rect.origin.\x  <= rect.origin.\x  + 1;
    rect.origin.y <= rect.origin.y + 2;
    rect.size.\x  <= 8'd100;
    rect.size.y <= 8'd200;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    // Target a single escaped struct member in $dumpvars.
    $dumpvars(1, rect.origin.\x );
    $dumpvars(1, \pt .\y );
  end
endmodule

module sub #(
    parameter int ADD
)(
    input int cyc
);
  int value;
  always_comb value = cyc + ADD;
endmodule
