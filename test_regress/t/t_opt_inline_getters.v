// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  int m_val;
  static int s_val;

  function new(int val);
    m_val = val;
  endfunction

  // Automatic method, read using 'return'
  function int get_return();
    return m_val;
  endfunction

  // Automatic method, read using IEEE 'name = variable'
  function int get_assign();
    get_assign = m_val;
  endfunction

  // Static method, read using 'return'
  static function int sget_return();
    return s_val;
  endfunction

  // Static method, read using IEEE 'name = variable'
  static function int sget_assign();
    sget_assign = s_val;
  endfunction
endclass

// Virtual getters must dispatch to the override
class VirtBase;
  int m_base = 1;
  virtual function int get();
    return m_base;
  endfunction
endclass

class VirtExt extends VirtBase;
  int m_ext = 2;
  virtual function int get();
    return m_ext;
  endfunction
endclass

// Getter of a base class must read the base member even if the derived class shadows it
class ShadowBase;
  int m_val = 1;
  function int get();
    return m_val;
  endfunction
endclass

class ShadowExt extends ShadowBase;
  int m_val = 2;
endclass

// Functions that look similar but are not getters
class NotGetter;
  int m_val = 5;
  NotGetter m_other;
  function void void_copy();
    m_val = m_val;
  endfunction
  function void other_set();
    m_other.m_val = m_val;
  endfunction
  function int other_set_ret();
    m_other.m_val = m_val;
  endfunction
  function NotGetter self();
    return this;
  endfunction
  function int get();
    return m_val;
  endfunction
endclass

function automatic NotGetter make_not_getter();
  automatic NotGetter ng = new;
  return ng;
endfunction

// Implicit 'this' call from a derived class where the member is shadowed
class ImplicitBase;
  int m_val = 1;
  function int get();
    return m_val;
  endfunction
endclass

class ImplicitExt extends ImplicitBase;
  int m_val = 2;
  function int call_get();
    return get();
  endfunction
endclass

module t;
  initial begin
    automatic Cls c1 = new(10);
    automatic Cls c2 = new(20);
    Cls::s_val = 30;
    `checkd(c1.get_return(), 10);
    `checkd(c2.get_return(), 20);
    `checkd(c1.get_assign(), 10);
    `checkd(c2.get_assign(), 20);
    c1.m_val = 11;
    `checkd(c1.get_return(), 11);
    `checkd(c1.get_assign(), 11);
    `checkd(c2.get_assign() + c1.get_return(), 31);
    `checkd(Cls::sget_return(), 30);
    `checkd(Cls::sget_assign(), 30);
    `checkd(c1.sget_return(), 30);
    Cls::s_val = 31;
    `checkd(Cls::sget_return(), 31);
    `checkd(c2.sget_assign(), 31);
    begin
      automatic VirtExt ve = new;
      automatic VirtBase vb = ve;
      `checkd(vb.get(), 2);
      `checkd(ve.get(), 2);
    end
    begin
      automatic ShadowExt se = new;
      automatic ShadowBase sb = se;
      `checkd(sb.get(), 1);
      `checkd(se.get(), 1);
      `checkd(se.m_val, 2);
    end
    begin
      automatic NotGetter ng = new;
      ng.m_other = new;
      ng.void_copy();
      ng.other_set();
      `checkd(ng.m_other.m_val, 5);
      ng.m_val = 6;
      void'(ng.other_set_ret());
      `checkd(ng.m_other.m_val, 6);
      `checkd(make_not_getter().get(), 5);
      `checkd(ng.self().get(), 6);
    end
    begin
      automatic ImplicitExt ie = new;
      `checkd(ie.call_get(), 1);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
