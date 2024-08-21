// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
   int x;

   static function Foo get;
      Foo foo = new;
      return foo;
   endfunction
endclass

module t;
   initial void'(Foo::get().randomize(x));
endmodule
