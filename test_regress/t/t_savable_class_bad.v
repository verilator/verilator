// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int imembera;
endclass : Cls

module t;
   initial begin
      Cls c;
      if (c != null) $stop;
      c = new;
      c.imembera = 10;
      if (c.imembera != 10) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
