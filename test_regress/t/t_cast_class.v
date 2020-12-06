// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base;
   int b;
endclass
class BaseExtended extends Base;
   int e;
endclass

module t;

   Base v_cls_a;
   BaseExtended v_cls_ab;
   BaseExtended v_cls_ab1;

   initial begin
      v_cls_a = Base'(null);
      if (v_cls_a != null) $stop;

      v_cls_ab = new;
      v_cls_ab.b = 10;
      v_cls_ab.e = 20;

      v_cls_ab1 = BaseExtended'(v_cls_ab);
      if (v_cls_ab1.b != 10) $stop;
      if (v_cls_ab1.e != 20) $stop;

      v_cls_a = Base'(v_cls_ab);
      if (v_cls_a.b != 10) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
