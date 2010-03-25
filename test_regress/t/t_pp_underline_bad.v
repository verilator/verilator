// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t;
   // verilator_no_inline_module
   initial $stop; // Should have failed
endmodule
