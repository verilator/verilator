// DESCRIPTION: Verilator: SystemVerilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   enum logic [2:0] {S0, S1, S2} state;

   initial begin
      state = S1;

      unique case (state)
        S0: $stop;
        S2: $stop;
      endcase
   end
endmodule
