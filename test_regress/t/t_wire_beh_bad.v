// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Wilson Snyder.

module t (/*AUTOARG*/);

   wire w;
   reg  r;

   assign r = 1'b1;
   always @ (r) w = 1'b0;

endmodule
