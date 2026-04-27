// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// This test checks if only necessary parts of class hierarchy emit to_string().
// The following class hierarchy should result in only 2 to_string()s emitted if the
// only printed object is of type Derived1 (only Derived1 and Base should emit
// to_string()):
//    V---- Base ----V
// Derived1      Derived2
//                   V
//               Derived3

class Base;
    int base_a;
endclass

class Derived1 extends Base;
    int derived1_a;
endclass

class Derived2 extends Base;
    int derived2_a;
endclass

class Derived3 extends Derived2;
    int derived3_a;
endclass

module t;
    Derived1 d1;

  initial begin
    d1 = new;

    $display("'%p'", d1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
