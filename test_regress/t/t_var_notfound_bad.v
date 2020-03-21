// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   integer i;
   integer a_var;

   sub sub ();

   task nottask(); endtask
   function int notfunc(); return 0; endfunction

   initial begin
      nf = 0;  // z not found
      sub.subsubz.inss = 0;  // subsub not found
      i = nofunc();  // nofunc not found
      i = sub.nofuncs();  // nofuncs not found
      notask();  // notask not found
      a_var();  // Calling variable as task
      $finish;
   end
endmodule

module sub;
   subsub subsub ();
   function int notfuncs(); return 0; endfunction
endmodule

module subsub;
   integer inss;
endmodule
