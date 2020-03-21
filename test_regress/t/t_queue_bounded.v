// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   int q[$ : 2];  // Shall not go higher than [2], i.e. size 3

   initial begin
      q.push_front(3);
      if (q.size() != 1) $stop;
      q.push_front(2);
      if (q.size() != 2) $stop;
      q.push_front(1);
      if (q.size() != 3) $stop;
      q.push_front(0);
      if (q.size() != 3) $stop;
      if (q[0] != 0) $stop;
      if (q[1] != 1) $stop;
      if (q[2] != 2) $stop;

      q.delete();
      q.push_back(0);
      q.push_back(1);
      q.push_back(2);
      if (q.size() != 3) $stop;
      q.push_back(3);
      if (q.size() != 3) $stop;
      if (q[0] != 0) $stop;
      if (q[1] != 1) $stop;
      if (q[2] != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
