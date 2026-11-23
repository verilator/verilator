// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Patrick O'Neill
// SPDX-License-Identifier: CC0-1.0

typedef logic [3:0] logic4_t;
typedef bit [1:0][3:0] bit2x4_t;

module t;
  localparam logic [7:0] WITH_X = 8'bx0x0_x1x1;
  // Cast to a packed array must clean every element
  localparam logic [7:0] CAST_TO_BIT = bit2x4_t'(WITH_X);

  // Needs a typedef passed through three levels of type parameters
  level1 #(.T(logic4_t)) u1 ();

  initial begin
    if (CAST_TO_BIT !== 8'b0000_0101) $stop;
    if (u1.u2.u3.ONES !== 4'b1111) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module level1 #(
    parameter type T = logic
);
  level2 #(.T(T)) u2 ();
endmodule

module level2 #(
    parameter type T = logic
);
  level3 #(.T(T)) u3 ();
endmodule

module level3 #(
    parameter type T = logic,
    parameter T ONES = T'('1)
);
endmodule
