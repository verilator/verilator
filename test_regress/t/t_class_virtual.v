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

virtual class uvm_phase;
   virtual function int exec_func;
      return 0;
   endfunction
endclass

class uvm_topdown_phase extends uvm_phase;
   function int get1;
      return exec_func();
   endfunction
endclass

class uvm_build_phase extends uvm_topdown_phase;
   virtual function int exec_func;
      return 1;
   endfunction
endclass

virtual class Cls;
   uvm_phase ph;
endclass

class ExtendsCls extends Cls;
   function new;
      uvm_build_phase bp = new;
      ph = bp;
   endfunction

   function int get1;
      return super.ph.exec_func();
   endfunction
endclass

module t;
   initial begin
      VA va = new;
      VB vb = new;
      VBase b;

      uvm_build_phase ph;
      ExtendsCls ec;

      if (va.hello() != 2) $stop;
      if (vb.hello() != 3) $stop;

      b = va;
      if (b.hello() != 2) $stop;
      b = vb;
      if (b.hello() != 3) $stop;

      ph = new;
      if (ph.get1() != 1) $stop;

      ec = new;
      if (ec.get1() != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
