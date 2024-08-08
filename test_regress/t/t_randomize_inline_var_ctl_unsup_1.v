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
   initial begin
      Foo foo = Foo::get();
      Foo foos[] = new[1];
      void'(foo.randomize(Foo::get().x));
      void'(foo.randomize(foos[0].x));
      void'(foo.randomize(null));
   end
endmodule
