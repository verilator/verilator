// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface class Icls1;
   pure virtual function int icfboth;
endclass

interface class Icls2;
   pure virtual function int icfboth;
endclass

interface class IclsBoth extends Icls1, Icls2;
   pure virtual function int icfboth;
endclass

class Cls implements IclsBoth;
   virtual function int icfboth;
      return 3;
   endfunction
endclass

module t(/*AUTOARG*/);

   Cls c;

   initial begin
      c = new;
      if (c.icfboth() != 3) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
