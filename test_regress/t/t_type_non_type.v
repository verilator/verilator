// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//      $write("*-* All Finished *-*\n");
//      $finish;
// on success, or $stop.
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
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
