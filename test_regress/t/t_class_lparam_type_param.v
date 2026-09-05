// DESCRIPTION: Verilator: Verilog Test module
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class types_c #(
    parameter int W = 8
);
  typedef logic [W-1:0] t;
  typedef logic signed [W-1:0] type1_t;
  typedef type1_t [W-1:0] type2_t;
endclass

module type_scope #(
    parameter type C = types_c#(8)
) ();
  C::t value;
  child #(.T(C::t)) u_child (.a_i('0));
  initial assert ($bits(value) == 8);
endmodule

module child #(
    parameter type T = logic
) (
    input T a_i
);
endmodule

module t;
  localparam int W = 8;

  // Class-scoped type via a localparam type, passed to a child type parameter.
  localparam type t_param = types_c#(W)::t;
  child #(.T(t_param)) u (.a_i('0));
  type_scope u_type_scope ();

  // Class-scoped type via a module-body typedef alias of a nested typedef.
  typedef types_c#(W)::type2_t t_alias;
  t_alias v;

  initial begin
    v = '0;
    assert ($bits(t_param) == 8);
    assert ($bits(t_alias) == 64);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
