// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Krzysztof Boronski.
// SPDX-License-Identifier: CC0-1.0

module t ();
   int array[1] = '{ 0 };
   initial begin
      $display(array[0]++);
      $display(array[0]);
      $display(++array[0]);
      $finish();
   end
endmodule
