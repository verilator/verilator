// DESCRIPTION: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

process p;  // force importing std into top-level namespace

class C;
   function new;
      if (randomize() != 1) $stop;
   endfunction
endclass

module t;
   initial begin
      automatic C c = new;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
