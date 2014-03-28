// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/);
   wire ok = 1'b0;
   sub sub (.ok(ok), , .nc());
endmodule

module sub (input ok, input none, input nc, input missing);
   initial if (ok && none && nc && missing) begin end  // No unused warning
endmodule
