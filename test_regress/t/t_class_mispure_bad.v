// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

virtual class Base;
   pure virtual function void pvfunc();
endclass

class Bar extends Base;
   // Bad, no implementation of pvfunc
endclass

module t;
   initial begin
      Bar obj = new();
      obj.pvfunc();
      $stop;
   end
endmodule
