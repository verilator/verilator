// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;

   initial begin
      automatic int q[$] = {1, 2};

      if (!(1 inside {q[0], q[1]})) $stop;
      if (3 inside {q[0], q[1]}) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
