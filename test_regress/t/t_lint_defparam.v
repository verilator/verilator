// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t;

   sub sub ();
   defparam sub.P = 2;

endmodule

module sub;
   parameter P = 6;
endmodule
