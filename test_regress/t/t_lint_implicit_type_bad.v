// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class imp_Cls_conflict;
endclass

module t;
   typedef int imp_typedef_conflict;
   localparam type imp_PARAM_conflict;

`default_nettype wire
   assign imp_typedef_conflict = 1'b1;
   assign imp_Cls_conflict = 1'b1;
   assign imp_PARAM_conflict = 1'b1;
endmodule
