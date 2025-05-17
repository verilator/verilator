// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

extern program ex_pgm;
extern interface ex_ifc;
extern module ex_mod;

module t(/*AUTOARG*/);

   ex_pgm u_pgm();
   ex_ifc u_ifc();
   ex_mod u_mod();

   initial begin
      ex_task();
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
