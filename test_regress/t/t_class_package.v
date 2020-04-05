// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkga;
  int pvar;
  class MyClass;
     int member;
     function int getpvar(); return pvar; endfunction
  endclass
endpackage

package pkgb;
  int pvar;
  class MyClass;
     int member;
     function int getpvar(); return pvar; endfunction
     function int getavar(); return pkga::pvar; endfunction
  endclass
endpackage

module t (/*AUTOARG*/);
   initial begin
      pkga::MyClass a;
      pkgb::MyClass b;

      pkga::pvar = 100;
      pkgb::pvar = 200;
      if (pkga::pvar != 100) $stop;
      if (pkgb::pvar != 200) $stop;

      a = new;
      b = new;
      a.member = 10;
      b.member = 20;
      if (a.member != 10) $stop;
      if (b.member != 20) $stop;

      if (a.getpvar() != 100) $stop;
      if (b.getpvar() != 200) $stop;
      if (b.getavar() != 100) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
