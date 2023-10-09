// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "t_vlt_warn_file_bad_b.vh"

module t;
   sub sub();
   int warn_t = 64'h1;
endmodule
