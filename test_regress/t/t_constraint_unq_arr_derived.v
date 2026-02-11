// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef enum bit [4:0] {
  ZERO = 5'b00000,
  RA, SP, GP, TP, T0, T1, T2, S0, S1, A0, A1, A2, A3, A4, A5, A6, A7,
  S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, T3, T4, T5, T6
} EnumType;

class Base;
  rand EnumType b_scratch_reg;
  rand EnumType b_pmp_reg[2];
  rand EnumType b_sp;
  rand EnumType b_tp;

  constraint b_example_constraint {
    unique {b_pmp_reg};
    {b_pmp_reg[0] > 0};
    {b_pmp_reg[0] < 3};
    {b_pmp_reg[1] > 0};
    {b_pmp_reg[1] < 3};
  }
endclass

class Foo extends Base;
  rand EnumType scratch_reg;
  rand EnumType pmp_reg[2];
  rand EnumType sp;
  rand EnumType tp;

  constraint example_constraint {
    unique {pmp_reg};
    {pmp_reg[0] > 0};
    {pmp_reg[0] < 3};
    {pmp_reg[1] > 0};
    {pmp_reg[1] < 3};
  }
endclass

module t;
  Foo foo;
  initial begin
    foo = new;
    repeat(100) if (foo.randomize() != 1 || foo.pmp_reg[0] == foo.pmp_reg[1]) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
