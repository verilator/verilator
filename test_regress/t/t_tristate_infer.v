// DESCRIPTION: Verilator: Verilog Test module
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module top (input a);
   mod m (.*);
endmodule

module mod (input a);
   initial assert (a !== 'z);
endmodule 

