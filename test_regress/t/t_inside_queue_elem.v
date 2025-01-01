// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   initial begin
      int q[$] = {1, 2};
      if (!(1 inside {q[0], q[1]})) $stop;
      if (3 inside {q[0], q[1]}) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
