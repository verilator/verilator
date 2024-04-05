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
   static function void isst();
   endfunction
endclass

class Bar;
   function void bar();
      Cls::nonstatic();  // <--- bad static ref
      Cls::isst();
   endfunction
endclass

class Extends extends Cls;
   function void ok();
      nonstatic();
      isst();
   endfunction
   static function extstatic();
      nonstatic();  // <--- bad static ref
      isst();
   endfunction
endclass

module t;
   function nonclassfunc();
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
