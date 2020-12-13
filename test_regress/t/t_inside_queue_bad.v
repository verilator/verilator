// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   int q[$];
   int assoc[int];
   int dyn[];
   bit m;

   initial begin
      m = (10 inside {q});
      m = (10 inside {assoc});
      m = (10 inside {dyn});
   end

endmodule
