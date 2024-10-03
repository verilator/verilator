// DESCRIPTION: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

process p;  // force importing std into top-level namespace

class C;
   function new;
      if (randomize() != 1) $stop;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      C c = new;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
