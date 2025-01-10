// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   typedef int imp_type_conflict;

`default_nettype wire
   assign imp_type_conflict = 1'b1;
endmodule
