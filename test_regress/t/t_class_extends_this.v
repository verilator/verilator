// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Base;
   class BaseInner;
      int value = 10;
      function void test;
         if (value != 10) $stop;
         if (this.value != 10) $stop;
         value = 20;
         if (value != 20) $stop;
         this.value = 30;
         if (value != 30) $stop;
      endfunction
   endclass

   int value = 1;
   BaseInner inner = new;
   function void test;
      if (value != 1) $stop;
      if (this.value != 1) $stop;
      value = 2;
      if (value != 2) $stop;
      this.value = 3;
      if (value != 3) $stop;
   endfunction
endclass

class Cls extends Base;
   class BaseInner extends Base::BaseInner;
      int value = 100;
      function void test;
         if (value != 100) $stop;
         if (this.value != 100) $stop;
         if (super.value != 10) $stop;
         super.test();
         if (value != 100) $stop;
         if (this.value != 100) $stop;
         if (super.value != 30) $stop;
         value = 200;
         if (value != 200) $stop;
         this.value = 300;
         if (value != 300) $stop;
      endfunction
   endclass

   int value = 20;
   BaseInner inner = new;
   function void test;
      if (value != 20) $stop;
      if (this.value != 20) $stop;
      if (super.value != 1) $stop;

      super.test();
      if (this.value != 20) $stop;

      super.value = 9;
      this.value = 29;
      if (super.value != 9) $stop;
      if (value != 29) $stop;

      inner.test();
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      c = new;
      c.test();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
