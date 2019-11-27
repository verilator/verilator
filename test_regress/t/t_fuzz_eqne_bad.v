// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

//bug1587
module t;
   reg a[0];
   reg b;
   reg c;
   initial c = (a != &b);
endmodule
