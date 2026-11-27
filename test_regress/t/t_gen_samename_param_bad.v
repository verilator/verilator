// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nick Brereton
// SPDX-License-Identifier: CC0-1.0

interface bus_if #(
    parameter int W = 1
);
  logic [W-1:0] d;
endinterface

class C #(
    parameter int W = 1
);
  static function int get();
    return W;
  endfunction
endclass

module sub #(
    parameter int W = 1,
    parameter type T = logic
);
endmodule

module core_a;
  int only_a;
endmodule

module core_b;
  int only_b;
endmodule

module mid #(
    parameter int R = 1
);
  if (R == 1) begin : g
    logic [7:0] x;
    typedef enum {A = 3} e_t;
    function automatic int f();
      return 8;
    endfunction
    core_a u_core ();
  end
  else begin : g
    logic [15:0] x;
    typedef enum {A = 5} e_t;
    function automatic int f();
      return 16;
    endfunction
    core_b u_core ();
  end

  sub #(.W($bits(g.x))) s_bits ();
  sub #(.W(g.x)) s_var ();
  sub #(.T(type(g.x))) s_type ();
  sub #(.W(g.A)) s_enum ();
  sub #(.W(g.f())) s_func ();
  sub #(.W($bits(g.u_core.only_a))) s_core ();
  sub s_dbits ();
  defparam s_dbits.W = $bits(g.x);
  sub s_denum ();
  defparam s_denum.W = g.A;
  localparam int L = g.A;
  bus_if #(.W($bits(g.x))) i_bits ();
  bus_if #(.W(g.A)) i_enum ();
  bus_if #(.W(g.f())) i_func ();
  C #($bits(g.x)) c_bits;
  initial $display("%0d", C#(g.A)::get());
endmodule

module t;
  mid #(.R(1)) u_r1 ();
  mid #(.R(2)) u_r2 ();
endmodule
