// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

import "DPI-C" context function void dpii_check();

module t (/*AUTOARG*/);
   initial begin
      dpii_check();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
