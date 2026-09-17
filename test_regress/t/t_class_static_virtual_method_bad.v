// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Foo;
  static virtual task foo();
  endtask
endclass

// Subtle case where virtual is implicit
typedef class Base;
class Derived extends Base;  // Before Base declared
  static task vimplicit();
  endtask
endclass

class Base;
  virtual task vimplicit();
  endtask
endclass

class Derived2 extends Base;  // After Base declared
  static task vimplicit();
  endtask
endclass
