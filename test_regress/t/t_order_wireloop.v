// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2005 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   bar
   );

   wire  foo;
   output  bar;

   // Oh dear.
   assign  foo = bar;
   assign  bar = foo;

endmodule
