// DESCRIPTION: Verilator: Verilog Test module
//
// A test of the +verilog2001ext+ and +verilog2005ext+ flags.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

// verilator lint_off SYMRSVDWORD

module t(input do);
   t_langext_order_sub sub (.do(do));
endmodule
