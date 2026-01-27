// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

function static int func();
   int cnt = 0;
   return ++cnt;
endfunction

module t;

   int   a;
   initial begin
      a = func;
      $stop;
   end

endmodule
