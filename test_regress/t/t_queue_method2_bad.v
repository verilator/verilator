// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   initial begin
      int q[$];
      int qe[$];  // Empty
      int qv[$];  // Value returns
      int qi[$];  // Index returns

      q = '{2, 2, 4, 1, 3};

      qi = q.find(a,b) with (0);  // b is extra
      qi = q.find(1) with (0);  // 1 is illegal

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
