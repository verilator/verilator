// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
endclass

package Pkg;
   // Issue #2956
   typedef string STYPE;
   typedef string line;
   task automatic testf;
      inout STYPE line;
   endtask
endpackage

module t;
   localparam type T = Cls;

   // Issue #2412
   typedef T this_thing;  // this_thing now a type

   function T newer();
      T this_thing;  // this_thing now a class reference
      this_thing = new;
      return this_thing;
   endfunction

   initial begin
      Cls c;
      c = newer();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
