// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base;
endclass
class Other;
endclass
enum { ZERO } e;

module t (/*AUTOARG*/);

   int i;
   int v;
   Base b;
   Other o;
   initial begin
      i = $cast(v, 1);  // 1
      i = $cast(b, b);  // 1
      i = $cast(b, o);  // 0
      i = $cast(e, 0);  // 1
      i = $cast(e, 10);  // 0
   end

endmodule
