// DESCRIPTION: Verilator: Dependent module parameter types converge before specialization
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Petr Nohavica
// SPDX-License-Identifier: CC0-1.0

class ModuleElement #(int W = 2);
  typedef logic [W-1:0] value_t;
endclass

module DependentModule #(
    int W = 3,
    int D = W + 2,
    type T = ModuleElement#(D)::value_t,
    type U = T,
    int N = $bits(U) + 4
) (
    output U value
);
  assign value = U'(N);
endmodule

module t;
  logic [6:0] value;
  DependentModule #(.W(5)) dut (.*);

  initial begin
    if ($bits(value) != 7) $stop;
    if (dut.N != 11) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
