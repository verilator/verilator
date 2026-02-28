// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module m1;
  m3 u_13 ();
  initial $display("liba:m1 %%m=%m %%l=%l");
endmodule

module m3;  // Module name duplicated between libraries
  initial $display("liba:m3 %%m=%m %%l=%l");
endmodule
