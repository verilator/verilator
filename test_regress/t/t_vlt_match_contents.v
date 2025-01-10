// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Ethan Sifferman.
// SPDX-License-Identifier: CC0-1.0

string MATCH_VERSION = "10.20";

module t;
   logic usignal_contents_suppress;  // Suppressed with -contents
   logic usignal_contents_mismatch;  // Doesn't match -contents
endmodule
