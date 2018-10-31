// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Wilson Snyder.

// Make sure type errors aren't suppressable
// verilator lint_off WIDTH

module t(ref int bad_primary_ref
         /*AUTOARG*/);
endmodule
