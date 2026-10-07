// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t_waiveroutput;
  reg width_warn = 2'b11;  // Width warning - must be line 8

  // verilator lint_off UNUSEDSIGNAL
  // verilator lint_off WIDTHTRUNC
  reg width_warn2 = 2'b11;
  // verilator lint_on WIDTHTRUNC
  reg [3:0] width_digits = 4'hDF;
  reg [3:0] width_expand = 1'b1;
  reg [63:0] width_xz = 'hx;
  // verilator lint_on UNUSEDSIGNAL
endmodule
