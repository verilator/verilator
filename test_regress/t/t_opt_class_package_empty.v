// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class EmptyBase;
  int m_a = 1;
  virtual function int get();
    return m_a;
  endfunction
endclass

class EmptyDerived extends EmptyBase;
  int m_b = 2;
  virtual function int get();
    return m_a + m_b;
  endfunction
endclass

class StaticVar;
  static int s_count = 0;
  function new();
    ++s_count;
  endfunction
endclass

class StaticFunc;
  static function int twice(int x);
    return 2 * x;
  endfunction
endclass

class StaticVoid;
  static function void call();
    $display("StaticVoid::call");
  endfunction
endclass

class Outer;
  class Inner;
    static int s_value = 5;
  endclass
  int m_c = 4;
endclass

class OuterStatic;
  static int s_value = 6;
  class InnerEmpty;
    int m_d = 7;
  endclass
endclass

class StaticBase;
  static int s_e = 9;
endclass

class PlainDerived extends StaticBase;
endclass

class ParamClass #(
    int N = 4
);
  int m_f = N;
endclass

class LocalParam;
  localparam int L = 3;
  int m_g = L;
endclass

class UnpackedStruct;
  typedef struct {
    int a;
    int b;
  } u_t;
  u_t m_h;
endclass

interface ifc;
  int x = 0;
  function void setx(int v);
    x = v;
  endfunction
endinterface

module t;
  ifc i0 ();
  ifc i1 ();

  initial begin
    EmptyBase base;
    EmptyDerived derived;
    StaticVar sv1;
    StaticVar sv2;
    Outer outer;
    OuterStatic::InnerEmpty innerEmpty;
    PlainDerived plainDerived;
    ParamClass paramClass;
    LocalParam localParam;
    UnpackedStruct unpackedStruct;
    virtual ifc vif;

    derived = new;
    base = derived;
    `checkd(base.get(), 3);
    base = new;
    `checkd(base.get(), 1);

    sv1 = new;
    sv2 = new;
    `checkd(StaticVar::s_count, 2);

    `checkd(StaticFunc::twice(21), 42);

    StaticVoid::call();

    outer = new;
    `checkd(outer.m_c, 4);
    `checkd(Outer::Inner::s_value, 5);

    innerEmpty = new;
    `checkd(innerEmpty.m_d, 7);
    `checkd(OuterStatic::s_value, 6);

    plainDerived = new;
    `checkd(plainDerived.s_e, 9);

    paramClass = new;
    `checkd(paramClass.m_f, 4);

    localParam = new;
    `checkd(localParam.m_g, 3);

    unpackedStruct = new;
    unpackedStruct.m_h.a = 8;
    `checkd(unpackedStruct.m_h.a, 8);

    vif = i1;
    vif.setx(11);
    `checkd(i0.x, 0);
    `checkd(i1.x, 11);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
