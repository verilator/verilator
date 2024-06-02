// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface class Icempty;
endclass : Icempty

package Pkg;
class Icls1 #(parameter PARAM = 12);
   localparam LP1 = 1;
   function int getParam();
      return PARAM;
   endfunction
endclass

endpackage

class Cls12 extends Pkg::Icls1;
endclass

module t(/*AUTOARG*/);

   Cls12 cp12;

   initial begin
      cp12 = new;
      if (cp12.getParam() != 12) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
