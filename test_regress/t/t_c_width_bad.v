// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   bit [99:0] wide = $c100("0");

   initial $display("%d", wide);

endmodule
