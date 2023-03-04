// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   enum logic [2:0] {
          e0,
          e1,
          e2,
          e3
        } EN;

   initial begin

      unique case (EN)
        e0 :;
        e1 :;
        e2 :;
        e3 :;
      endcase

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
