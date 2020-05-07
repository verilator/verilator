// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

`define DUP fred
`define DUP barney

`define DUPP paramed(x) (x)
`define DUPP paramed(x,z) (x*z)

     initial $stop; // Should have failed

endmodule
