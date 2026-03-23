// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  string s = "a string";
  int vec[2];
  initial begin
    $display("%d %x %f %t", s, s, s, s);
    $display("%D %X %F %T", s, s, s, s);
    $display("%d %x %f %t", vec, vec, vec, vec);
    $display("%D %X %F %T", vec, vec, vec, vec);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
