// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

function integer f;
   static integer i = 0;
   return ++i;
endfunction

module t;
   initial begin
      $display("%d", f());
      $display("%d", f());
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
