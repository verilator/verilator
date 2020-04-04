// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Alex Solomatnikov
// SPDX-License-Identifier: CC0-1.0

module t;
   sub #(.REAL(2.0)) sub;
endmodule

module sub ();
   timeunit 1ns;
   timeprecision 1ps;

   parameter REAL = 0.0;

   initial begin
      $display("REAL %g", REAL);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
