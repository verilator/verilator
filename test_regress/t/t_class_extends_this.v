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
      value = 2;
      if (value != 2) $stop;
      this.value = 3;
      if (value != 3) $stop;
   endfunction
endclass

class Cls extends Base;
   int value = 20;
   function void test;
      if (value != 20) $stop;
      if (this.value != 20) $stop;
      if (super.value != 1) $stop;

      super.test();
      if (this.value != 20) $stop;

      super.value = 9;
      this.value = 29;
      if (super.value != 9) $stop;
      if (value != 29) $stop;;
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
