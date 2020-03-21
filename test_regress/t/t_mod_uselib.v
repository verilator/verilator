// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

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
