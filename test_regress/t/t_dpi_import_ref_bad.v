// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  import "DPI-C" function void dpii_ref(ref int a);
  import "DPI-C" task dpii_const_ref(input int b, const ref int c);
endmodule
