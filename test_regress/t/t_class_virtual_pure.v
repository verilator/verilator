// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

virtual class VBase;
   pure virtual function int hello();
endclass

class VA extends VBase;
   virtual function int hello;
      return 2;
   endfunction
endclass

module t;
   initial begin
      VA va = new;
      if (va.hello() != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
