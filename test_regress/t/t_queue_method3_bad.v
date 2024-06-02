// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   typedef struct packed { int x, y; } point;
   initial begin
      point points_q[$];
      point points_qv[$];
      points_q.push_back(point'{1, 2});

      // `index` should be treated as normal member select,
      // but the member is not present in the struct
      points_qv = points_q.find_first(a) with (a.x.index == 0);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
