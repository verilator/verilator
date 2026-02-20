// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t_multitop1s;
   initial $display("In '%m'");
endmodule

module in_subfile;
   initial $display("In '%m'");
endmodule
