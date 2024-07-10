// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   randc bit [37:0] i;
endclass

module t (/*AUTOARG*/);
   Cls c;
   initial begin
      c = new;
      c.randomize;
   end
endmodule
