// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/);

   integer i;

   sub sub ();

   initial begin
      nf = 0;  // z not found
      sub.subsubz.inss = 0;  // subsub not found
      i = nofunc();  // nofunc not found
      notask();  // notask not found
      $finish;
   end
endmodule

module sub;
   subsub subsub ();
endmodule

module subsub;
   integer inss;
endmodule
