// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   wire foo;
   wire bar;

   sub sub (.*, .*);

   sub sub (foo, .*);

   sub sub (foo, .bar);

endmodule

module sub (input foo, input bar);
endmodule
