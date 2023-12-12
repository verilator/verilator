// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   int q[$] = '{1, 2, 3};
   bit dyn[] = '{0, 0};

   initial begin
      if (!(1 inside {q})) $stop;
      if (4 inside {q}) $stop;
      if (!(4 inside {q, 4})) $stop;

      if (!(0 inside {dyn})) $stop;
      if (1 inside {dyn}) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
