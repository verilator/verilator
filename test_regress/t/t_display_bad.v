// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   reg [40:0] disp; initial disp = 41'ha_bbbb_cccc;
   initial begin
      // Display formatting
      $display("%x");  // Too few
      $display("%x",disp,disp);  // Too many
      $display("%q");  // Bad escape
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
