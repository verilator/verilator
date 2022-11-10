// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
      clk
   );

   input clk;

   function bit test_find;
      string bar[$];
      string found[$];
      bar.push_back("baz");
      bar.push_back("qux");
      found = bar.find(x) with (x == "baz");
      return found.size() == 1;
   endfunction

   function bit test_find_index;
      int    q[$] = {1, 2, 3, 4};
      int    found[$] = q.find_index(x) with (x <= 2);
      return found.size() == 2;
   endfunction

   function bit test_find_first_index;
      int    q[] = {1, 2, 3, 4, 5, 6};
      int    first_even_idx[$] = q.find_first_index(x) with (x % 2 == 0);
      return first_even_idx[0] == 1;
   endfunction

   function bit test_sort;
      int    q[] = {-5, 2, -3, 0, 4};
      q.sort(x) with (x >= 0 ? x : -x);
      return q[1] == 2;
   endfunction

   always @(posedge clk) begin
      bit [3:0] results = {test_find(), test_find_index(),
                           test_find_first_index(), test_sort()};
      if (results == '1) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Results: %b\n", results);
         $stop;
      end
   end
endmodule
