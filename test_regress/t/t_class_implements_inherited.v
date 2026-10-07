// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Kristof Marien
// SPDX-License-Identifier: CC0-1.0

// A derived class may satisfy inherited pure virtual interface methods through
// concrete implementations inherited from its base class.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package if_pkg;
  interface class top_if;
    pure virtual function void set_value(string value);
    pure virtual function int get_a();
  endclass

  interface class mid_if extends top_if;
    pure virtual function int get_b();
  endclass

  interface class leaf_if extends mid_if;
    pure virtual function int get_c();
  endclass
endpackage

class base_cls implements if_pkg::mid_if;
  extern virtual function void set_value(string value);
  extern virtual function int get_a();
  extern virtual function int get_b();
endclass

function void base_cls::set_value(string value);
endfunction

function int base_cls::get_a();
  return 11;
endfunction

function int base_cls::get_b();
  return 22;
endfunction

class derived_cls extends base_cls implements if_pkg::leaf_if;
  extern virtual function void set_value(string value);
  extern virtual function int get_c();
endclass

function void derived_cls::set_value(string value);
endfunction

function int derived_cls::get_c();
  return 33;
endfunction

// Implementations two levels up
class grand_cls extends derived_cls implements if_pkg::leaf_if;
endclass

class pass_cls extends base_cls;
endclass

class from_pass_cls extends pass_cls implements if_pkg::mid_if;
endclass

// Implementations from a base class that does not implement the interface class
// (IEEE 1800-2023 8.26.2)
interface class other_if;
  pure virtual function int get_d(int x);
  pure virtual task get_e(output int v, input int x);
endclass

class plain_cls;
  extern virtual function int get_d(int x);
  virtual task get_e(output int v, input int x);
    v = 50 + x;
  endtask
endclass

function int plain_cls::get_d(int x);
  return 40 + x;
endfunction

class from_plain_cls extends plain_cls implements other_if;
endclass

class pass_plain_cls extends plain_cls;
endclass

class from_pass_plain_cls extends pass_plain_cls implements other_if;
endclass

// Implementation that is virtual because it overrides a virtual method (IEEE 1800-2023 8.20)
interface class f_if;
  pure virtual function int get_f();
endclass

class vbase_cls;
  virtual function int get_f();
    return 1;
  endfunction
endclass

class override_cls extends vbase_cls;
  function int get_f();
    return 60;
  endfunction
endclass

class from_override_cls extends override_cls implements f_if;
endclass

module t;
  initial begin
    derived_cls obj;
    grand_cls gobj;
    from_pass_cls pobj;
    from_plain_cls plobj;
    from_pass_plain_cls pplobj;
    from_override_cls ovobj;
    if_pkg::leaf_if ifc;
    if_pkg::mid_if mifc;
    other_if oifc;
    f_if fifc;
    int v;

    obj = new;
    ifc = obj;
    ifc.set_value("test");
    `checkd(ifc.get_a(), 11)
    `checkd(ifc.get_b(), 22)
    `checkd(ifc.get_c(), 33)

    gobj = new;
    ifc = gobj;
    `checkd(ifc.get_a(), 11)
    `checkd(ifc.get_b(), 22)
    `checkd(ifc.get_c(), 33)

    pobj = new;
    mifc = pobj;
    `checkd(mifc.get_a(), 11)
    `checkd(mifc.get_b(), 22)

    plobj = new;
    oifc = plobj;
    `checkd(oifc.get_d(1), 41)
    oifc.get_e(v, 2);
    `checkd(v, 52)

    pplobj = new;
    oifc = pplobj;
    `checkd(oifc.get_d(3), 43)
    oifc.get_e(v, 4);
    `checkd(v, 54)

    ovobj = new;
    fifc = ovobj;
    `checkd(fifc.get_f(), 60)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
