// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int x;
   function new;
      x = 1;
   endfunction
endclass

class ExtendCls extends Cls;
   function new;
      x = 2;
   endfunction
endclass

class AnotherExtendCls extends Cls;
   function new;
      x = 3;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls cls = new;
      ExtendCls ext_cls = new;
      AnotherExtendCls an_ext_cls = new;

      if (cls.x == 1) cls = ext_cls;
      else cls = an_ext_cls;
      if (cls.x != 2) $stop;

      if (cls.x == 1) cls = ext_cls;
      else cls = an_ext_cls;
      if (cls.x != 3) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
