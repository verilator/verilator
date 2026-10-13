// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Saqib Khan
// SPDX-License-Identifier: CC0-1.0

// Two-class cycle
class Cls2A extends Cls2B;
endclass
class Cls2B extends Cls2A;
endclass

// Three-class cycle
class Cls3A extends Cls3C;
endclass
class Cls3B extends Cls3A;
endclass
class Cls3C extends Cls3B;
endclass

// Interface class cycle
interface class IfcA extends IfcB;
endclass
interface class IfcB extends IfcA;
endclass

module t;
  Cls2A c2 = new;
  Cls3B c3 = new;
endmodule
