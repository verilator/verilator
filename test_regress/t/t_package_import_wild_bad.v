// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg;
  localparam int PKG_VALUE = 1;
endpackage

package pkg_reimport;
  import pkg::PKG_VALUE;  // Imported but not exported, so not suggested
endpackage

module t;
  import pkg_reimport::*;
  import pkg::*;
  int x = PKG_VALEU;  // <--- Error: misspelled, suggests wildcard imported name
endmodule
