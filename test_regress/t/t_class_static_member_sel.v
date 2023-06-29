// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
   static int x = 1;
endclass

class Bar;
   Foo f;
   function new;
      f = new;
   endfunction
endclass

class Baz;
   function static Bar get_bar;
      Bar b = new;
      return b;
   endfunction
endclass

class IntWrapper;
   int        x;
endclass

class Cls;
   static IntWrapper iw;
   function new;
      if (iw == null) iw = new;
   endfunction
endclass

class ExtendCls extends Cls;
endclass

class Getter1;
   function static int get_1;
      return 1;
   endfunction
endclass

class uvm_root;
   int x;
   static uvm_root m_inst;
   static function uvm_root get_inst();
      if (m_inst == null) m_inst = new;
      return m_inst;
   endfunction
   function int get_7();
      return 7;
   endfunction
endclass

module t (/*AUTOARG*/
   );

   initial begin
      Foo foo = new;
      Bar bar = new;
      Baz baz = new;
      ExtendCls ec = new;
      Getter1 getter1 = new;

      if (foo.x != 1) $stop;

      foo.x = 2;
      if (foo.x != 2) $stop;

      bar.f.x = 3;
      if (bar.f.x != 3) $stop;

      baz.get_bar().f.x = 4;
      if (baz.get_bar().f.x != 4) $stop;

      ec.iw.x = 5;
      if (ec.iw.x != 5) $stop;

      if (getter1.get_1 != 1) $stop;

      uvm_root::get_inst().x = 6;
      if (uvm_root::get_inst().x != 6) $stop;

      if (uvm_root::get_inst().get_7() != 7) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
