// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
  extern task func_bad();  //<--- Error (mismatch func)
  extern function int f1_bad();  //<--- Error (mismatch func type)
  extern function int f2_bad();  //<--- Error (mismatch func type)
  extern function void f3_bad();  //<--- Error (mismatch func type)
  extern function void f1bit_bad(int a);  //<--- Error (mismatch arg type)
  extern function void f2args1_bad(bit a);  //<--- Error (missing arg)
  extern function void f2args2(bit a);  // ok
  extern function void f2args3_bad(bit a, bit b, bit c);  //<--- Error (missing arg)
  extern function void farg_name_bad(bit declnamebad);  //<--- Error (declname arg)
endclass

function bit Cls::func_bad();
  return 1'b0;
endfunction

function bit Cls::f1_bad();
  return 1'b0;
endfunction
function void Cls::f2_bad();
endfunction
function bit Cls::f3_bad();
  return 1'b0;
endfunction

function void Cls::f1bit_bad(bit a);
endfunction

function void Cls::f2args1_bad(bit a, bit b);
endfunction

function void Cls::f2args2(bit a, bit b);
endfunction

function void Cls::f2args3_bad(bit a, bit b);
endfunction

function void Cls::farg_name_bad(bit declname);
endfunction

module t;
  initial $stop;
endmodule
