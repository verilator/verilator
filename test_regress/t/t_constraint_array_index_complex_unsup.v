// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A shift of a signed narrow value below a nonzero base is ambiguous: widening
// demotes an arithmetic shift onto a logical one, so neither reading is provable
// and both spellings are a compile-time error.

class C1;
  rand byte r;
  bit [7:0] pool[5:270];
  constraint c { r == -4; pool[r>>>1] == 8'h77; }
endclass

class C2;
  rand byte r;
  bit [7:0] pool[5:270];
  constraint c { r == -4; pool[r>>1] == 8'h77; }
endclass

// A reduction over widened arithmetic hides the widening from the normalizer:
// the sign of the extension is unprovable, so this is an error.
class C3;
  rand byte r8;
  bit [7:0] pool[5:12];
  constraint c { r8 == 8; pool[((&(r8+32'h1))+5)] == 8'h77; }
endclass

// Same hidden widening, but nested as a right-hand operand instead.
class C4;
  rand byte r8;
  bit [7:0] pool[5:12];
  constraint c { r8 == 8; pool[(10-(&(r8+32'h1)))] == 8'h77; }
endclass

// Same hidden widening, but nested as a conditional result instead.
class C5;
  rand bit f;
  rand byte r8;
  bit [7:0] pool[5:12];
  constraint c { f == 1; r8 == 8; pool[(f?0:(&(r8+32'h1)))] == 8'h77; }
endclass

// An ambiguous shift nested as a right-hand operand: same error as above.
class C6;
  rand byte r;
  bit [7:0] pool[5:270];
  constraint c { r == -4; pool[(10-(r>>1))] == 8'h77; }
endclass

// An ambiguous shift nested as a conditional result: same error as above.
class C7;
  rand bit f;
  rand byte r;
  bit [7:0] pool[5:270];
  constraint c { f == 1; r == -4; pool[(f?0:(r>>1))] == 8'h77; }
endclass

module t;
  initial begin
    C1 obj1;
    C2 obj2;
    C3 obj3;
    C4 obj4;
    C5 obj5;
    C6 obj6;
    C7 obj7;
    obj1 = new;
    obj2 = new;
    obj3 = new;
    obj4 = new;
    obj5 = new;
    obj6 = new;
    obj7 = new;
    if (obj1.randomize() == 0) $stop;
    if (obj2.randomize() == 0) $stop;
    if (obj3.randomize() == 0) $stop;
    if (obj4.randomize() == 0) $stop;
    if (obj5.randomize() == 0) $stop;
    if (obj6.randomize() == 0) $stop;
    if (obj7.randomize() == 0) $stop;
  end
endmodule
