// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module pre_no_ts;
endmodule

`timescale 1ns/1ns

module t;
   pre_no_ts pre_no_ts();
   post_no_ts pst_no_ts();
endmodule

module post_no_ts;
endmodule
