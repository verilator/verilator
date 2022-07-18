// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Cls;
   integer imembera;
   integer imemberb;
endclass : Cls

module t (/*AUTOARG*/);

   initial begin
      string a [*];
      string k;
      string v;

      Cls x;

      v = a.num("badarg");
      v = a.size("badarg");
      v = a.exists();  // Bad
      v = a.exists(k, "bad2");
      a.delete(k, "bad2");

      a.sort;  // Not legal on assoc
      a.rsort;  // Not legal on assoc
      a.reverse;  // Not legal on assoc
      a.shuffle;  // Not legal on assoc

      a.first;  // Not legal on wildcard
      a.last;  // Not legal on wildcard
      a.next;  // Not legal on wildcard
      a.prev;  // Not legal on wildcard
      a.unique_index;  // Not legal on wildcard
      a.find_index;  // Not legal on wildcard
      a.find_first_index;  // Not legal on wildcard
      a.find_last_index;  // Not legal on wildcard

      a[x] = "bad";
   end
endmodule
