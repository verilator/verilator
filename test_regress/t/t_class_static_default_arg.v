// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Foo;
   static function bit get_first(bit q[$] = {1'b1});
      return q[0];
   endfunction
endclass

module t;

   initial begin
      bit first;
      automatic bit arg[$] = {1'b0, 1'b1};
      first = Foo::get_first();
      if (first != 1) $stop;
      first = Foo::get_first(arg);
      if (first != 0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
