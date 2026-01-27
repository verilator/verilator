// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
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
