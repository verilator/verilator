// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Base1;
   int s = 2;
   function new(int def = 3);
      s = def;
   endfunction
endclass

class Cls1 extends Base1(default);
   // Gets new(int def)
endclass

module t;
   initial begin
      Cls1 c1;
      Cls1 c5;
      c1 = new(57);
      if (c1.s !== 57) $stop;

      c5 = new;
      if (c5.s !== 5) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
