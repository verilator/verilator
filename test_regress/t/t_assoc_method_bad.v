// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   initial begin
      string a [string];
      string k;
      string v;

      v = a.num("badarg");
      v = a.size("badarg");
      v = a.exists();  // Bad
      v = a.exists(k, "bad2");
      v = a.first();  // Bad
      v = a.next(k, "bad2");  // Bad
      v = a.last();  // Bad
      v = a.prev(k, "bad2");  // Bad
      a.delete(k, "bad2");

      a.sort;  // Not legal on assoc
      a.rsort;  // Not legal on assoc
      a.reverse;  // Not legal on assoc
      a.shuffle;  // Not legal on assoc
   end
endmodule
