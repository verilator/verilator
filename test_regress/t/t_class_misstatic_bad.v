// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
  int m_field = get_ok();
  function int get_ok();
    return 1;
  endfunction
  function void nonstatic();
  endfunction
  function Cls nonstatic_retcls();
    return null;
  endfunction
  static function void isst();
  endfunction
endclass

class Bar;
  function void bar();
    Cls::nonstatic();  // <--- bad static ref
    Cls::nonstatic_retcls();  // <--- bad static ref
    Cls::isst();
  endfunction
endclass

class Extends extends Cls;
  function void ok();
    nonstatic();
    isst();
  endfunction
  static function void extstatic();
    nonstatic();  // <--- bad static ref
    isst();
  endfunction
  function new();
    Cls c = super.nonstatic_retcls();
  endfunction
endclass

module t;
  function void nonclassfunc();
    Cls::nonstatic();  // <--- bad static ref
    Cls::isst();
  endfunction
  initial begin
    Bar obj = new();
    obj.bar();
    Cls::nonstatic();  // <--- bad static ref
    Cls::isst();
    Extends::isst();
    $stop;
  end
endmodule
