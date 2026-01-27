// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
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
