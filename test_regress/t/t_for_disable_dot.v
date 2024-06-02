// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   int i;

   initial begin
      begin : named
         for (i = 0; i < 10; ++i) begin : loop
            if (i == 5) disable t.named;
         end
      end
      if (i != 5) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
