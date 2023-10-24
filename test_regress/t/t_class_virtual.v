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

class VA extends VBase;
   virtual function int hello;
      return 2;
   endfunction
endclass

class VB extends VBase;
   virtual function int hello;
      return 3;
   endfunction
endclass

bit passed = 1'b0;

virtual class uvm_phase;
   virtual function void exec_func;
   endfunction
endclass

class uvm_topdown_phase extends uvm_phase;
   function void traverse;
      exec_func();
   endfunction
endclass

class uvm_build_phase extends uvm_topdown_phase;
   virtual function void exec_func;
      passed = 1'b1;
   endfunction
endclass

module t;
   initial begin
      VA va = new;
      VB vb = new;
      VBase b;

      uvm_build_phase ph;

      if (va.hello() != 2) $stop;
      if (vb.hello() != 3) $stop;

      b = va;
      if (b.hello() != 2) $stop;
      b = vb;
      if (b.hello() != 3) $stop;

      ph = new;
      ph.traverse();
      if (!passed) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
