// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Geza Lore
// SPDX-License-Identifier: CC0-1.0

module t(
  output wire res
);

   function automatic logic foo(logic bar);
      foo = '0;
   endfunction

   logic       a, b;
   logic [0:0][1:0] array;

   assign b = 0;
   assign a = foo(b);
   assign res = array[a][a];

endmodule
