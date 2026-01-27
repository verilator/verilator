// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

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
