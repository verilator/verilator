// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

import "DPI-C" context function void dpii_check();

module t;
   initial begin
      dpii_check();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
