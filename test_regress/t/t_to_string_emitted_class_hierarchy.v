// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

//  Base
//    V
// Derived1----------------  IClass1
//    V                   V  V
// Derived2------      Derived7
//    V         V         V
// Derived3  Derived5  Derived8
//    V         V         V
// Derived4  Derived6  Derived9

interface class IClass1;
endclass

class Base;
  int base_field;
endclass

class Derived1 extends Base;
  int derived1_field;
endclass

class Derived2 extends Derived1;
  int derived2_field;
endclass

class Derived3 extends Derived2;
  int derived3_field;
endclass

class Derived4 extends Derived3;
  int derived4_field;
endclass

class Derived5 extends Derived2;
  int derived5_field;
endclass

class Derived6 extends Derived5;
  int derived6_field;
endclass

class Derived7 extends Derived1 implements IClass1;
  int derived7_field;
endclass

class Derived8 extends Derived7;
  int derived8_field;
endclass

class Derived9 extends Derived8;
  int derived9_field;
endclass

module t;
  `OBJ_TYPE obj = new;
  `PRINTED_FROM_TYPE printed_obj = obj;
`ifdef OBJ_TYPE2
  `OBJ_TYPE2 obj2 = new;
  `PRINTED_FROM_TYPE2 printed_obj2 = obj2;
`endif

  initial begin
  $display("'%p'", printed_obj);
`ifdef OBJ_TYPE2
  $display("'%p'", printed_obj2);
`endif

  $write("*-* All Finished *-*\n");
  $finish;
  end
endmodule
