// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

module t (/*AUTOARG*/);
   sub sub ();
endmodule

module sub #(parameter WIDTH=X, parameter X=WIDTH)
   ();
endmodule
