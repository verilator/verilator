// DESCRIPTION: Verilator: Unsupported tristate constructur error
//
// This is a compile only regression test of tristate handling for bug514
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [11:0] ck;

   assign ck[1:0] = {1'bz,{1{1'b0}}};

   test i_test (.clk (ck[1:0]));

endmodule


module test (clk);

   output wire [1:0] clk;

endmodule // test
