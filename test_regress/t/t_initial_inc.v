// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

`define foo bar
`ifdef foo
 `ifdef baz `else
// Test file to make sure includes work;
   integer user_loaded_value;
 `endif
`endif
