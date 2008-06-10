// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t;

`define DUP fred
`define DUP barney

`define DUPP paramed(x) (x)
`define DUPP paramed(x,z) (x*z)

     initial $stop; // Should have failed

endmodule
