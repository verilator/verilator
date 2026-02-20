// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Class1 #(
    type T
);
  typedef T::Some_type2 Some_type1;
endclass

class Class2;
  typedef int Some_type2;
endclass

module t;
  initial begin
    automatic int value0 = 7;
    automatic Class1#(Class2)::Some_type1 value1 = value0;
    automatic int value2 = value1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
