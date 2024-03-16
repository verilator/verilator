// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int f;
   function new(int x);
      f = x;
   endfunction
endclass

class ExtendCls extends Cls;
   function new(int x);
      super.new(x);
   endfunction
endclass

class AnotherExtendCls extends Cls;
   function new(int x);
      super.new(x);
   endfunction
endclass

class ExtendExtendCls extends ExtendCls;
   function new(int x);
      super.new(x);
   endfunction
endclass

module t (/*AUTOARG*/);
   typedef ExtendCls ExtendCls_t;

   initial begin
      Cls cls1 = null, cls2 = null;
      ExtendCls_t ext_cls = null;
      AnotherExtendCls an_ext_cls = null;
      ExtendExtendCls ext_ext_cls = null;
      int r;

      cls1 = (cls1 == null) ? cls2 : cls1;
      if (cls1 != null) $stop;

      cls1 = new(1);
      cls1 = (cls1 == null) ? cls2 : cls1;
      if (cls1.f != 1) $stop;

      cls1 = (cls1 != null) ? cls2 : cls1;
      if (cls1 != null) $stop;

      cls1 = new(1);
      cls2 = new(2);
      cls1 = (cls1 != null) ? cls2 : cls1;
      if (cls1.f != 2) $stop;

      cls1 = null;
      cls1 = (ext_cls != null) ? ext_cls : cls2;
      if (cls1.f != 2) $stop;

      ext_cls = new(3);
      cls1 = (ext_cls != null) ? ext_cls : cls2;
      if (cls1.f != 3) $stop;

      ext_ext_cls = new(4);
      an_ext_cls = new(5);
      cls1 = (ext_ext_cls.f != 4) ? ext_ext_cls : an_ext_cls;
      if (cls1.f != 5) $stop;

      ext_cls = new(3);
      r = $random;
      cls1 = r[0] ? ext_cls : null;
      if (cls1 != null && cls1.f != 3) $stop;

      ext_cls = new(3);
      r = $random;
      cls1 = r[0] ? null : ext_cls;
      if (cls1 != null && cls1.f != 3) $stop;

      ext_cls = new(3);
      r = $random;
      cls1 = r[0] ? null : null;
      if (cls1 != null) $stop;

      ext_cls = new(3);
      cls1 = (ext_cls == null) ? null : null;
      if (cls1 != null) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
