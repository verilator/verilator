// DESCRIPTION: Verilator: Cyclic dependent class parameters
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Petr Nohavica
// SPDX-License-Identifier: CC0-1.0

class SelfType #(
    type A = A
);
  typedef A out_t;
endclass

class SelfValue #(
    int A = A + 1,
    type T = logic [A-1:0]
);
  typedef T out_t;
endclass

class NestedValue #(
    int A = NestedValue#()::M
);
  localparam int M = A;
endclass

module t;
  SelfType#()::out_t a;
  SelfValue#()::out_t b;
  localparam int C = NestedValue#()::M;
endmodule
