// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

program t(/*AUTOARG*/);
   initial begin
      $write("*-* All Finished *-*\n");
      $exit;  // Must be in program block
   end
endprogram
