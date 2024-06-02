// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   static function bit get_true();
      return 1'b1;
   endfunction

   static function bit test_find_index_in_class();
      if (get_true) begin
         int q[$] = {0, -1, 3, 1, 4, 1};
         int found_idx[$];
         found_idx = q.find_index(node) with (node == 1);
         return found_idx[0] == 3;
      end
      return 0;
   endfunction
endclass

module t (/*AUTOARG*/
   );

   function bit test_find;
      string bar[$];
      string found[$];
      bar.push_back("baz");
      bar.push_back("qux");
      found = bar.find(x) with (x == "baz");
      return found.size() == 1;
   endfunction

   function static bit test_find_index;
      int    q[$] = {1, 2, 3, 4};
      int    found[$] = q.find_index(x) with (x <= 2);
      return found.size() == 2;
   endfunction

   function static bit test_find_first_index;
      int    q[] = {1, 2, 3, 4, 5, 6};
      int    first_even_idx[$] = q.find_first_index(x) with (x % 2 == 0);
      return first_even_idx[0] == 1;
   endfunction

   function bit is_even(int a);
      return a % 2 == 0;
   endfunction

   function static bit test_find_first_index_by_func;
      int    q[] = {1, 2, 3, 4, 5, 6};
      int    first_even_idx[$] = q.find_first_index(x) with (is_even(x));
      return first_even_idx[0] == 1;
   endfunction

   function automatic bit test_sort;
      int    q[] = {-5, 2, -3, 0, 4};
      q.sort(x) with (x >= 0 ? x : -x);
      return q[1] == 2;
   endfunction

   initial begin
      if (!test_find()) $stop;
      if (!test_find_index()) $stop;
      if (!test_find_first_index()) $stop;
      if (!test_find_first_index_by_func()) $stop;
      if (!test_sort()) $stop;
      if (!Cls::test_find_index_in_class()) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
