// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
   int member;

   task method; endtask
endclass

module t;
   initial begin
      Foo foo = new;
      Foo::member = 1;
      Foo::method();
   end
endmodule
