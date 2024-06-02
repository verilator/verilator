// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class A;
   extern function void method();
endclass

class B;
   extern function void method();
endclass

class C;
   extern function void method();
endclass

class D;
   extern function void method();
endclass

function void A::method();
   B obj = new;
   obj.method();
endfunction

function void B::method();
   this.srandom(0);
endfunction

function void C::method();
   this.srandom(0);
endfunction

function void D::method();
   C obj = new;
   obj.method();
endfunction

module t;
   A obj1 = new;
   D obj2 = new;
   initial begin
      obj1.method();
      obj2.method();
   end
endmodule
