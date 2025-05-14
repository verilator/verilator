// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

typedef int arr_t[5][3];

class Cls;
   int cnt;
   int init_depth;
   function arr_t get_arr(int depth);
      arr_t arr = (depth > 1) ? get_arr(depth - 1) : '{5{'{init_depth, init_depth * 2, init_depth * 3}}};
      cnt++;
      return arr;
   endfunction
endclass

module t (/*AUTOARG*/);
   Cls c = new;
   initial begin
      arr_t arr;
      c.init_depth = 5;
      arr = (c.init_depth > 0) ? c.get_arr(5) : '{5{'{1, 2, 3}}};

      if (arr[0][0] != 5) $stop;
      if (arr[0][1] != 10) $stop;
      if (arr[0][2] != 15) $stop;
      if (arr[3][2] != 15) $stop;

      if (c.cnt != 5) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
