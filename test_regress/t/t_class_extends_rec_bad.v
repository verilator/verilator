// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class RecursiveExtCls extends RecursiveExtCls;
   int i;
endclass

module t (/*AUTOARG*/);
   RecursiveExtCls cls = new;
endmodule
