// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef enum bit [4:0] {V0 = 1} my_enum;
class Cls;
  my_enum sp = V0;
endclass

module t;
  initial begin
    Cls c;
    int i;
    c = new;
    if (i inside {c.sp}) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
