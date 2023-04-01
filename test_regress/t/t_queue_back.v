// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   int q[$];
   int r;

   initial begin
      q = { 20, 30, 40 };

      r = q[$];
      if (r != 40) $stop;

      r = q[$-1];
      if (r != 30) $stop;

      q = q[0:$-1]; // void'(q.pop_back()) or q.delete(q.size-1)
      if (q.size != 2) $stop;
      if (q[0] != 20) $stop;
      if (q[1] != 30) $stop;

      q = { 20, 30, 40 };
      q = q[$-1:$];
      if (q.size != 2) $stop;
      if (q[0] != 30) $stop;
      if (q[1] != 40) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
