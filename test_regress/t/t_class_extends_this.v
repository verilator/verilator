// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Base;
   int value = 1;
   function void test;
      if (value != 1) $stop;
      if (this.value != 1) $stop;
   endfunction
endclass

class Cls extends Base;
   int value = 2;
   function void test;
      if (value != 2) $stop;
      if (this.value != 2) $stop;
      if (super.value != 1) $stop;
      super.test();
      super.value = 10;
      this.value = 20;
      if (super.value != 10) $stop;
      if (value != 20) $stop;;
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
