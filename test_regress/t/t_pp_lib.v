// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

`include "t_pp_lib_inc.vh"
module t();
   wire [`WIDTH-1:0] a;
   library_cell n1(a);
endmodule
