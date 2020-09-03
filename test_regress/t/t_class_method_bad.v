// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base1;
   task meth1; endtask
endclass

class Cls2 extends Base1;
   task meth2; endtask
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls2 c;
      c.meth3();  // Not found
   end
endmodule
