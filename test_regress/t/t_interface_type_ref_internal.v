// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ifc #(parameter int width)(input logic [width-1:0] b);
  logic [width-1:0] a;
  typedef logic[width-1:0] type_t;
  always_comb a = type_t'(b);
endinterface

module t;
  logic [15:0] x;
  ifc #(.width(16)) x_ifc(x);
  logic [7:0] y;
  ifc #(.width(8)) y_ifc(y);

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
