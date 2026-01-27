// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class RecursiveExtCls extends RecursiveExtCls;
   int i;
endclass

module t;
   RecursiveExtCls cls = new;
endmodule
