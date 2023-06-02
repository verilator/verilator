// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls1;
endclass

class Cls2;
endclass

class ExtCls1;
endclass

module t (/*AUTOARG*/);
   Cls1 c1;
   Cls2 c2;
   ExtCls1 ext_c1;

   initial begin
      c1 = (c1 != null) ? c1 : c2;
      c1 = (c1 != null) ? c2 : c2;
      c2 = (c1 == null) ? 1'b1 : c2;
      ext_c1 = (c1 == null) ? ext_c1 : c1;
   end
endmodule
