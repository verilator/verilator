// DESCRIPTION: Verilator: SystemVerilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   enum logic [2:0] {S0, S1, S2} state;

   int v = 0;

   initial begin
      state = S1;

      unique case (state)
        S0, S2: $stop;
        S1: v++;
      endcase
      unique case (state)
        S2: $stop;
        default: v++;
      endcase
   end
endmodule
