// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t (/*AUTOARG*/);
//   // `uselib {dir=<lib_diry> | file=<lib_file> | libext=<file_ext> | lib=<lib_name>
`uselib libext=.v
   s s ();
endmodule

module s;
  initial begin
     $write("*-* All Finished *-*\n");
     $finish;
   end
endmodule
