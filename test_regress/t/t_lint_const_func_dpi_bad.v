// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Donald Owen.
// SPDX-License-Identifier: CC0-1.0

module t ();
   import "DPI-C" function int dpiFunc();
   localparam PARAM = dpiFunc();
endmodule
