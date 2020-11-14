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
      qv = q.unique with (1);  // Bad no with allowed
      q.reverse(1);  // Bad no args allowed
      q.shuffle(1);  // Bad no args allowed
      qv = q.find;  // Bad missing with
      qv = q.find_first;  // Bad missing with
      qv = q.find_last;  // Bad missing with
      qi = q.find_index;  // Bad missing with
      qi = q.find_first_index;  // Bad missing with
      qi = q.find_last_index;  // Bad missing with

      qi = q.size with (1);  // with not allowed

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
