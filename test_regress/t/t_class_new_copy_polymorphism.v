// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test that `new <handle>` (shallow copy) preserves the runtime type
// of the source object, per IEEE 1800-2017 8.7.

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Base;
  int value;
  function new();
    value = 10;
  endfunction
  virtual function string get_type();
    return "BASE";
  endfunction
  virtual function int get_id();
    return 1;
  endfunction
endclass

class Derived extends Base;
  int extra;
  function new();
    super.new();
    value = 20;
    extra = 99;
  endfunction
  virtual function string get_type();
    return "DERIVED";
  endfunction
  virtual function int get_id();
    return 2;
  endfunction
endclass

class GrandChild extends Derived;
  function new();
    super.new();
    value = 30;
    extra = 88;
  endfunction
  virtual function string get_type();
    return "GRANDCHILD";
  endfunction
  virtual function int get_id();
    return 3;
  endfunction
endclass

module t;
  initial begin
    Base b;
    Derived d;
    Base copy;

    // Test 1: Copy via base handle pointing to Derived
    d = new();
    b = d;
    copy = new b;
    `checks(copy.get_type(), "DERIVED");
    `checkd(copy.get_id(), 2);
    `checkd(copy.value, 20);

    // Test 2: Verify it's a true copy (not alias)
    copy.value = 999;
    `checkd(d.value, 20);

    // Test 3: Copy via base handle pointing to GrandChild
    begin
      GrandChild gc;
      gc = new();
      b = gc;
      copy = new b;
      `checks(copy.get_type(), "GRANDCHILD");
      `checkd(copy.get_id(), 3);
      `checkd(copy.value, 30);
    end

    // Test 4: Copy of base-type object (no polymorphism, still works)
    begin
      Base b2;
      Base copy2;
      b2 = new();
      copy2 = new b2;
      `checks(copy2.get_type(), "BASE");
      `checkd(copy2.get_id(), 1);
      `checkd(copy2.value, 10);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
