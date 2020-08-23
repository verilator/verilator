// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

virtual class VBase;
   virtual function int hello;
      return 1;
   endfunction
endclass

`ifndef VERILATOR
virtual class VA extends VBase;
   virtual function int hello;
      return 2;
   endfunction
endclass

virtual class VB extends VBase;
   virtual function int hello;
      return 3;
   endfunction
endclass

module t;
   initial begin
      VA va = new;
      VB vb = new;
      VBase b;
      b = va;
      if (b.hello() != 2) $stop;
      b = vb;
      if (b.hello() != 3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
`endif
