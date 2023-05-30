// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   int p[15] = '{9, 8, 3, 2, 1, 5, 5, 5, 4, 1, 7, 4, 6, 9, 10};

   initial begin
      $display("array:            %p", p);
      $display("find:             %p", p.find(x) with (x <= 5));
      $display("find_index:       %p", p.find_index(x) with (x == 5));
      $display("find_first:       %p", p.find_first(x) with (x > 5));
      $display("find_first_index: %p", p.find_first_index(x) with (x == 5));
      $display("find_last:        %p", p.find_last(x) with (x > 5));
      $display("find_last_index:  %p", p.find_last_index(x) with (x == 5));
      $display("min:              %p", p.min());
      $display("max:              %p", p.max());
      $display("unique:           %p", p.unique());
      $display("unique_index:     %p", p.unique_index());
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
