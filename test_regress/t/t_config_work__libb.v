// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module m2;
  m3 u_23 ();
  initial $display("libb:m2 %%m=%m %%l=%l");
endmodule

module m3;  // Module name duplicated between libraries
  initial $display("libb:m3 %%m=%m %%l=%l");
endmodule
