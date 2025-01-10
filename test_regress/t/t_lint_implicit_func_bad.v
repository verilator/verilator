// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   function void imp_func_conflict();
   endfunction

`default_nettype wire
   assign imp_func_conflict = 1'b1;
endmodule
