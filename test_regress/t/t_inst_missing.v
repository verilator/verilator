// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/);
   wire ok = 1'b0;
   // verilator lint_off PINNOCONNECT
   sub sub (.ok(ok), .nc());
   // verilator lint_on PINNOCONNECT
endmodule

module sub (input ok, input nc);
   initial if (ok&&nc) begin end  // No unused warning
endmodule
