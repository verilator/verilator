// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg;
  localparam int PA = 1;
  localparam int PB = PA + 1;
endpackage

package pkg2;
  localparam int Q1 = Q2;  // <--- Error: before declaration
  localparam int Q2 = 5;
endpackage

class Cls;
  function int f();
    return CP;  // Class members may be referenced before their declaration
  endfunction
  localparam int CP = 4;
endclass

module sub #(
    parameter int W = 1
) (
    output logic [W-1:0] o
);
  assign o = '0;
endmodule

module t #(
    parameter int A = 2,
    parameter int B = A
) ();
  import pkg::*;

  real p;
  initial begin
    p = 1.0 * N;  // <--- Error: before declaration (issue #8894)
    $display("%f", p);
  end
  localparam int N = 8;

  function int g();
    return LP;  // <--- Error: before declaration
  endfunction
  localparam int LP = 7;

  generate
    if (1) begin : gb
      localparam int GP = GQ;  // <--- Error: before declaration
      localparam int GQ = 1;
    end
  endgenerate

  logic [W2-1:0] o2;  // <--- Error: before declaration
  sub #(.W(W2)) u_sub (.o(o2));  // <--- Error: before declaration
  localparam int W2 = 4;

  logic [PB-1:0] x;
  Cls c;
  initial $display(g(), x, pkg2::Q1, A, B, c.f(), gb.GP);
endmodule
