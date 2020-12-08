// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base;
endclass
class BasedA extends Base;
endclass
class BasedB extends Base;
endclass

module t (/*AUTOARG*/);
   int i;
   int a;
   int ao;

   Base b;
   Base bo;
   BasedA ba;
   BasedA bao;
   BasedB bb;
   BasedB bbo;

   // verilator lint_off CASTCONST

   initial begin
      a = 1234;
      i = $cast(ao, a);
      if (i != 1) $stop;
      if (ao != 1234) $stop;

      a = 12345;
      $cast(ao, a);
      if (ao != 12345) $stop;

      i = $cast(ao, 2.1 * 3.7);
      if (i != 1) $stop;
      if (ao != 8) $stop;

      i = $cast(bo, null);
      if (i != 1) $stop;
      if (bo != null) $stop;

      ba = new;
      b = ba;
      i = $cast(bao, b);
      if (i != 1) $stop;
      if (b != ba) $stop;

      bb = new;
      b = bb;
      i = $cast(bbo, b);
      if (i != 1) $stop;
      if (b != bb) $stop;

      bb = new;
      b = bb;
      bao = ba;
      i = $cast(bao, b);
      if (i != 0) $stop;
      if (bao != ba) $stop;  // Unchanged

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
