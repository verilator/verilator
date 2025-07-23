// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

import "DPI-C" pure function int identity(input int value);

module t;
   initial begin
      int n = 0;
      logic [127:0] val = 128'b1;
      logic [15:0] one = 16'b1;

      // This condition involves multiple wide temporaries, and an over-width
      // shift, all of which requires V3Premit to fix up.
      while (|((val[ 7'(one >> identity(32)) +: 96] << n) >> n)) begin
        ++n;
      end

      $display("n=%0d", n);
      if (n != 96) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
