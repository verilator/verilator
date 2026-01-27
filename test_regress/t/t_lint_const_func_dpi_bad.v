// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2021 Donald Owen
// SPDX-License-Identifier: CC0-1.0

module t ();
   import "DPI-C" function int dpiFunc();
   localparam PARAM = dpiFunc();
endmodule
