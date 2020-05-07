// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   // width warnings off due to command line
   wire A = 15'd1234;

   // width warnings off due to command line + manual switch
   // verilator lint_off WIDTH
   wire B = 15'd1234;

   // this turnon does nothing as off on command line
   // verilator lint_on WIDTH
   wire C = 15'd1234;

endmodule
