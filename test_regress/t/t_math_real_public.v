// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Alex Solomatnikov
// SPDX-License-Identifier: CC0-1.0

module t;
   sub #(.REAL_PARAM(2.0)) sub();
endmodule

module sub ();
   parameter REAL_PARAM = 0.0;  // Magic name grepped for in .py file

   initial begin
      $display("REAL_PARAM=%g", REAL_PARAM);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
