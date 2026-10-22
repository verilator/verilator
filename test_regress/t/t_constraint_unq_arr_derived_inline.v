// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
typedef enum bit [4:0] {
  ZERO = 5'b00000,
  RA, SP, GP, TP, T0, T1, T2, S0, S1, A0, A1, A2, A3, A4, A5, A6, A7,
  S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, T3, T4, T5, T6
} EnumType;
// verilog_format: on

class Base;
  rand EnumType b_scratch_reg;
  rand EnumType b_pmp_reg[2];
  rand EnumType b_sp;
  rand EnumType b_tp;
endclass

class Foo extends Base;
  rand EnumType scratch_reg;
  rand EnumType pmp_reg[2];
  rand EnumType sp;
  rand EnumType tp;
endclass

module t;
  Foo foo;
  initial begin
    foo = new;
    repeat (100)
    if (foo.randomize() with {
          unique {foo.pmp_reg};
          foo.pmp_reg[0] inside {1, 2};
          foo.pmp_reg[1] inside {1, 2};
        } != 1 || foo.pmp_reg[0] == foo.pmp_reg[1])
      $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
