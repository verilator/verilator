// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   function int f;
      fork
         return 0;  // Illegal 9.3.2
      join_none
   endfunction

   int i;

   initial begin
      i = f();
   end

endmodule
