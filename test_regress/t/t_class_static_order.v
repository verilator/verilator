// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class ClsZ;
   function new();
      $display("ClsZ::new");
   endfunction
endclass

class ClsA;
   function new();
      $display("ClsA::new");
   endfunction
   function void access;
      $display("ClsA::access");
   endfunction
endclass

class ClsB;
   static ClsZ z = new;
   function new();
      $display("ClsB::new");
   endfunction
   function void access;
      $display("ClsB::access");
   endfunction
endclass

class ClsC;
   // Elaboration will call these
   static ClsA a = new;
   static ClsB b = new;
   function new();
      $display("ClsC::new");
   endfunction
   function void access;
      $display("ClsC::access");
      a = new;
      a.access;
   endfunction
endclass

module t (/*AUTOARG*/);
   function void makec;
      ClsC c;
      $display("c = new;");
      c = new;
      $display("c.access;");
      c.access;
   endfunction
   initial begin
      $display("makec;");
      makec;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
