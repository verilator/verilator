// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef union packed {
   int x;
} Union;

class Cls;
   rand int assocarr[string];
   rand int dynarr[];
   rand int unpackarr[5];
   rand Union uni;
endclass

module t (/*AUTOARG*/);
   Cls obj;

   initial begin
      obj = new;
      obj.randomize();
   end
endmodule
