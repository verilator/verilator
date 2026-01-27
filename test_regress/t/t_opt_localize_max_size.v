// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2016 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   int x;
   initial begin
      x = $c32(1);
      $display(x);
      x = $c32(2);
      $display(x);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
