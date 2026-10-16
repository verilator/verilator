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

module t;
  initial begin
    derived_cls obj;
    if_pkg::leaf_if ifc;

    obj = new;
    ifc = obj;
    ifc.set_value("test");
    `checkd(ifc.get_a(), 11)
    `checkd(ifc.get_b(), 22)
    `checkd(ifc.get_c(), 33)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
